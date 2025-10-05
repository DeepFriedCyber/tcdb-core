from typing import List, Optional

class PipelineRequest:
    def __init__(self, data: List[List[float]], 
                 embedding_module: str = 'standard',
                 tda_module: str = 'rips',
                 downstream_module: Optional[str] = None,
                 labels: Optional[List[int]] = None):
        self.data = data
        self.embedding_module = embedding_module
        self.tda_module = tda_module
        self.downstream_module = downstream_module
        self.labels = labels

    @classmethod
    def from_dict(cls, data: dict):
        if 'data' not in data:
            raise ValueError("Missing required field: 'data'")

        return cls(
            data=data['data'],
            embedding_module=data.get('embedding_module', 'standard'),
            tda_module=data.get('tda_module', 'rips'),
            downstream_module=data.get('downstream_module'),
            labels=data.get('labels')
        )
