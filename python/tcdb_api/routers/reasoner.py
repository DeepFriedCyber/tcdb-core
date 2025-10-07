"""
Reasoner/Constraint checking endpoints
"""

from fastapi import APIRouter, HTTPException, status
from typing import List, Tuple, Dict, Any

from ..models import ReasonerRequest, ReasonerResponse, ViolationDetail

router = APIRouter(prefix="/reasoner", tags=["reasoner"])


def check_death_ge_birth(pd: List[Tuple[float, float]]) -> List[ViolationDetail]:
    """
    Check that all death times are >= birth times.
    
    This is a fundamental property of persistence diagrams.
    Features cannot die before they are born.
    """
    violations = []
    
    for i, (birth, death) in enumerate(pd):
        # Skip infinite features
        if death == float('inf') or str(death) == 'inf':
            continue
        
        if death < birth:
            violations.append(ViolationDetail(
                constraint="DeathGeBirth",
                detail=f"Point {i}: death ({death}) < birth ({birth})",
                severity="critical"
            ))
    
    return violations


def check_max_lifetime(pd: List[Tuple[float, float]], max_lifetime: float) -> List[ViolationDetail]:
    """
    Check that all feature lifetimes are <= max_lifetime.
    
    This filters noise or enforces physical constraints.
    """
    violations = []
    
    for i, (birth, death) in enumerate(pd):
        # Skip infinite features
        if death == float('inf') or str(death) == 'inf':
            continue
        
        lifetime = death - birth
        if lifetime > max_lifetime:
            violations.append(ViolationDetail(
                constraint=f"MaxLifetime:{max_lifetime}",
                detail=f"Point {i}: lifetime ({lifetime:.4f}) exceeds max ({max_lifetime})",
                severity="medium"
            ))
    
    return violations


def check_betti_non_negative(betti_data: Dict[str, Any]) -> List[ViolationDetail]:
    """
    Check that all Betti numbers are non-negative.
    
    Negative Betti numbers indicate a computational error.
    """
    violations = []
    
    if not betti_data:
        return violations
    
    # Check if betti_data has values
    if "values" in betti_data:
        for i, value in enumerate(betti_data["values"]):
            if value < 0:
                violations.append(ViolationDetail(
                    constraint="BettiNonNegative",
                    detail=f"Betti value {i}: {value} is negative",
                    severity="critical"
                ))
    
    return violations


def parse_constraint(constraint_str: str) -> Tuple[str, Dict[str, Any]]:
    """
    Parse a constraint string into name and parameters.
    
    Examples:
        "DeathGeBirth" -> ("DeathGeBirth", {})
        "MaxLifetime:1.5" -> ("MaxLifetime", {"max": 1.5})
    """
    if ":" in constraint_str:
        name, param = constraint_str.split(":", 1)
        try:
            param_value = float(param)
            return name, {"max": param_value}
        except ValueError:
            return name, {"param": param}
    else:
        return constraint_str, {}


@router.post(
    "/check",
    response_model=ReasonerResponse,
    summary="Check topological constraints",
    description="Validate persistence diagrams and Betti curves against constraints"
)
async def check_constraints(request: ReasonerRequest):
    """
    Check constraints on topological summaries
    
    This validates persistence diagrams and Betti curves against a set of
    mathematical constraints. Violations indicate either:
    - Computational errors in the TDA pipeline
    - Invalid input data
    - Physical impossibilities
    
    **Supported Constraints:**
    
    1. **DeathGeBirth**: Death time must be ≥ birth time for all features
       - Fundamental property of persistence diagrams
       - Violations indicate bugs in persistence computation
    
    2. **MaxLifetime:X**: Feature lifetime must be ≤ X
       - Filters noise or enforces physical bounds
       - Example: `MaxLifetime:1.5` rejects features with lifetime > 1.5
    
    3. **BettiNonNegative**: Betti numbers must be non-negative
       - Fundamental mathematical property
       - Violations indicate computational errors
    
    **Parameters:**
    - **constraints**: List of constraint names (e.g., ["DeathGeBirth", "MaxLifetime:1.5"])
    - **pd**: Persistence diagram as list of [birth, death] pairs
    - **betti**: Optional Betti curve data
    
    **Returns:**
    - **ok**: True if all constraints satisfied, False otherwise
    - **violations**: List of violations with details
    - **checked_constraints**: List of constraints that were checked
    
    **Example:**
    ```json
    {
        "constraints": ["DeathGeBirth", "MaxLifetime:1.5"],
        "pd": [[0.2, 0.9], [0.5, 1.0]],
        "betti": null
    }
    ```
    
    **Response (all constraints satisfied):**
    ```json
    {
        "ok": true,
        "violations": [],
        "checked_constraints": ["DeathGeBirth", "MaxLifetime:1.5"]
    }
    ```
    
    **Response (violations detected):**
    ```json
    {
        "ok": false,
        "violations": [
            {
                "constraint": "DeathGeBirth",
                "detail": "Point 1: death (0.4) < birth (0.5)",
                "severity": "critical"
            }
        ],
        "checked_constraints": ["DeathGeBirth", "MaxLifetime:1.5"]
    }
    ```
    """
    try:
        # Convert pd to list of tuples
        pd_tuples = [(birth, death) for birth, death in request.pd]
        
        all_violations = []
        checked = []
        
        # Check each constraint
        for constraint_str in request.constraints:
            constraint_name, params = parse_constraint(constraint_str)
            checked.append(constraint_str)
            
            if constraint_name == "DeathGeBirth":
                violations = check_death_ge_birth(pd_tuples)
                all_violations.extend(violations)
            
            elif constraint_name == "MaxLifetime":
                max_val = params.get("max", 1.0)
                violations = check_max_lifetime(pd_tuples, max_val)
                all_violations.extend(violations)
            
            elif constraint_name == "BettiNonNegative":
                violations = check_betti_non_negative(request.betti or {})
                all_violations.extend(violations)
            
            else:
                # Unknown constraint - skip with warning
                all_violations.append(ViolationDetail(
                    constraint=constraint_name,
                    detail=f"Unknown constraint: {constraint_name}",
                    severity="low"
                ))
        
        return ReasonerResponse(
            ok=len(all_violations) == 0,
            violations=all_violations,
            checked_constraints=checked
        )
    
    except Exception as e:
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail={"error": str(e)}
        )

