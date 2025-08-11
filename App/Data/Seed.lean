namespace App.Data

/-- Simple dataset container. -/
structure Dataset where
  vertices : List String
  edges    : List (String × String)
deriving Repr

/-- Classical proposition: include self-loops + explicit excludes. -/
def classical : Dataset :=
  { vertices := ["p","¬p"]
  , edges    := [("p","p"), ("¬p","¬p"), ("p","¬p"), ("¬p","p")] }

/-- Entailment chain p → q → r, with self-loops; a single exclusion for demo. -/
def entailment_chain : Dataset :=
  { vertices := ["p","q","r","¬r"]
  , edges    := [("p","p"), ("q","q"), ("r","r"), ("¬r","¬r"),
                 ("p","q"), ("q","r"),
                 ("r","¬r")] }  -- exclusion edge demo

/-- Superposition precursor (p branches to q and r, both to s). -/
def superposition_precursor : Dataset :=
  { vertices := ["p","q","r","s","¬s"]
  , edges    := [("p","p"), ("q","q"), ("r","r"), ("s","s"), ("¬s","¬s"),
                 ("p","q"), ("p","r"), ("q","s"), ("r","s"),
                 ("s","¬s")] } -- one exclusion

/-- EPR-style correlation sketch: A1↔B1, A2↔B2, plus self-loops. -/
def epr_correlation : Dataset :=
  { vertices := ["A1","A2","B1","B2","¬A1","¬B1"]
  , edges    := [("A1","A1"), ("A2","A2"), ("B1","B1"), ("B2","B2"),
                 ("¬A1","¬A1"), ("¬B1","¬B1"),
                 ("A1","B1"), ("B1","A1"),
                 ("A2","B2"), ("B2","A2"),
                 ("A1","¬A1"), ("B1","¬B1")] } -- exclusions for demo

end App.Data
