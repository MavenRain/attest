import AttestTwin

namespace F2NegFixture

axiom opaqueProof : AttestTwin.Equal

def unitArg (x : AttestTwin.LayoutOf opaqueProof) : PUnit := x

end F2NegFixture
