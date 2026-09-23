import AttestTwin

theorem checked (P : Prop) (p q : P) (G : P → Prop) (w : G p) : G q := w
