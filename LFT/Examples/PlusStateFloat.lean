def log2F (x : Float) : Float := Float.log x / Float.log 2.0
def entropy2F (ps : List Float) : Float :=
  ps.foldl (fun acc p => if p > 0.0 then acc - p * log2F p else acc) 0.0
#eval (let p1 := 3.0/5.0; let p2 := 2.0/5.0; let h := entropy2F [p1,p2]; (h, 2.0*h))
