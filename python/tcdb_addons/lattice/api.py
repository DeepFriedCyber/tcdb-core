
from dataclasses import dataclass

@dataclass(frozen=True)
class LatticeElement:
    value: str  # e.g., 'low'|'med'|'high'

class TrustLattice:
    order = ["low","med","high"]
    def join(self, a: LatticeElement, b: LatticeElement) -> LatticeElement:
        ia = self.order.index(a.value)
        ib = self.order.index(b.value)
        return LatticeElement(self.order[max(ia, ib)])

def merge_policy(*labels: LatticeElement) -> LatticeElement:
    if not labels:
        raise ValueError("merge_policy requires at least one label")
    lat = TrustLattice()
    out = labels[0]
    for x in labels[1:]:
        out = lat.join(out, x)
    return out
