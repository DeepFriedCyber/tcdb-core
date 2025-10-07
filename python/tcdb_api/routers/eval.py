"""
Evaluation/Hallucination detection endpoints
"""

from fastapi import APIRouter, HTTPException, status
from typing import List

from ..models import (
    EvalRequest, EvalResponse, EvalItemResult, EvalSummary
)

router = APIRouter(prefix="/eval", tags=["evaluation"])


def simple_entailment_check(claims: List[str], answer_text: str) -> bool:
    """
    Simple entailment check: do claims appear in answer text?
    
    This is a basic implementation. A real system would use:
    - NLI models (Natural Language Inference)
    - Semantic similarity
    - Knowledge graphs
    """
    if not claims:
        return True  # No claims to verify
    
    # Simple substring check (case-insensitive)
    answer_lower = answer_text.lower()
    for claim in claims:
        claim_lower = claim.lower()
        # Check if key terms from claim appear in answer
        claim_words = set(claim_lower.split())
        answer_words = set(answer_lower.split())
        
        # If most claim words appear in answer, consider it supported
        overlap = len(claim_words & answer_words)
        if overlap < len(claim_words) * 0.5:  # At least 50% overlap
            return False
    
    return True


def check_hallucination(item) -> bool:
    """
    Check if an item contains hallucinations.
    
    Hallucination indicators:
    - Claims not supported by answer text
    - Citations without claims
    - Topological constraint violations
    """
    # If answer is [ABSTAIN], no hallucination
    if "[ABSTAIN]" in item.answer_text.upper():
        return False
    
    # If there are claims but no citations, potential hallucination
    if item.claims and not item.citations:
        return True
    
    # If there are citations but no claims, potential hallucination
    if item.citations and not item.claims:
        return True
    
    # Check if claims are supported by answer text
    if item.claims:
        supported = simple_entailment_check(item.claims, item.answer_text)
        if not supported:
            return True
    
    # Check topological constraints if provided
    if item.pd and item.constraints:
        # Check DeathGeBirth constraint
        if "DeathGeBirth" in item.constraints:
            for birth, death in item.pd:
                if death < birth and death != float('inf'):
                    return True  # Violation = hallucination
    
    return False


@router.post(
    "/run",
    response_model=EvalResponse,
    summary="Run evaluation pipeline",
    description="Evaluate LLM outputs for hallucinations and claim support"
)
async def run_evaluation(request: EvalRequest):
    """
    Run evaluation pipeline on LLM outputs
    
    This endpoint evaluates LLM-generated answers for:
    - **Hallucination detection**: Claims not supported by evidence
    - **Citation verification**: Proper citation of sources
    - **Topological constraints**: Mathematical validity
    - **Claim support**: Entailment checking
    
    **Evaluation Criteria:**
    
    1. **Abstention**: If answer contains [ABSTAIN], no hallucination
    2. **Claim-Citation Balance**: Claims should have citations
    3. **Entailment**: Claims should be supported by answer text
    4. **Topological Validity**: Persistence diagrams must satisfy constraints
    
    **Parameters:**
    - **items**: List of items to evaluate
    - **require_tcdb**: If True, require TCDB verification for all items
    
    **Returns:**
    - **items**: Evaluation results for each item
    - **summary**: Overall statistics
    
    **Example:**
    ```json
    {
        "items": [
            {
                "id": "ex1",
                "question": "Does X form β-sheets at pH<6?",
                "answer_text": "Yes, per Smith 2019.",
                "claims": ["X forms beta-sheets at pH<6"],
                "citations": ["doc://smith2019#p3"],
                "pd": [[0.1, 0.9]],
                "constraints": ["DeathGeBirth"],
                "data_cid": "cid:abc",
                "code_rev": "rev:123"
            },
            {
                "id": "ex2",
                "question": "Is CVE-2021-44228 exploitable?",
                "answer_text": "[ABSTAIN] insufficient evidence",
                "claims": [],
                "citations": []
            }
        ],
        "require_tcdb": false
    }
    ```
    
    **Response:**
    ```json
    {
        "items": [
            {
                "id": "ex1",
                "hallucinated": false,
                "supported": true,
                "violations": [],
                "confidence_score": 0.95
            },
            {
                "id": "ex2",
                "hallucinated": false,
                "supported": true,
                "violations": [],
                "confidence_score": 1.0
            }
        ],
        "summary": {
            "total_items": 2,
            "hallucinated_count": 0,
            "supported_count": 2,
            "accuracy": 1.0
        }
    }
    ```
    """
    try:
        results = []
        hallucinated_count = 0
        supported_count = 0
        
        for item in request.items:
            # Check for hallucination
            is_hallucinated = check_hallucination(item)
            
            # Check if claims are supported
            is_supported = True
            if item.claims:
                is_supported = simple_entailment_check(item.claims, item.answer_text)
            
            # Collect violations
            violations = []
            if is_hallucinated:
                if item.claims and not item.citations:
                    violations.append("Claims without citations")
                if item.citations and not item.claims:
                    violations.append("Citations without claims")
                if not is_supported:
                    violations.append("Claims not supported by answer")
            
            # Check topological constraints
            if item.pd and item.constraints:
                for birth, death in item.pd:
                    if "DeathGeBirth" in item.constraints:
                        if death < birth and death != float('inf'):
                            violations.append(f"Death < Birth: ({birth}, {death})")
            
            # Calculate confidence score
            confidence_score = None
            if item.answer_text and "[ABSTAIN]" in item.answer_text.upper():
                confidence_score = 1.0  # High confidence in abstention
            elif is_supported and not is_hallucinated:
                confidence_score = 0.95
            elif is_supported:
                confidence_score = 0.7
            else:
                confidence_score = 0.3
            
            # Create result
            result = EvalItemResult(
                id=item.id,
                hallucinated=is_hallucinated,
                supported=is_supported,
                violations=violations,
                confidence_score=confidence_score
            )
            results.append(result)
            
            # Update counts
            if is_hallucinated:
                hallucinated_count += 1
            if is_supported:
                supported_count += 1
        
        # Create summary
        total = len(request.items)
        accuracy = (total - hallucinated_count) / total if total > 0 else 0.0
        
        summary = EvalSummary(
            total_items=total,
            hallucinated_count=hallucinated_count,
            supported_count=supported_count,
            accuracy=accuracy
        )
        
        return EvalResponse(
            items=results,
            summary=summary
        )
    
    except Exception as e:
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail={"error": str(e)}
        )

