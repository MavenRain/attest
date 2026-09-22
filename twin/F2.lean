import AttestTwin

namespace F2Fixture

set_option linter.defProp false in
def proof : AttestTwin.Equal := .refl trivial
axiom opaqueProof : AttestTwin.Equal

def keep (x : AttestTwin.LayoutOf proof) : AttestTwin.LayoutOf proof := x
def opaqueKeep (x : AttestTwin.LayoutOf opaqueProof) : AttestTwin.LayoutOf opaqueProof := x

example : AttestTwin.LayoutOf proof = PUnit := rfl

def pack (x : AttestTwin.LayoutOf proof) : Nat × AttestTwin.LayoutOf proof := (7, x)
def opaquePack (x : AttestTwin.LayoutOf opaqueProof) : Nat × AttestTwin.LayoutOf opaqueProof := (7, x)

end F2Fixture
