import LFT.Graphs

/-!
App-level edge classifier: decide id / entails / excludes.
Default behavior:
- id       : v = w
- excludes : false (you can change this later)
- entails  : anything else
-/

namespace App

def isId (v w : String) : Bool := v = w
def isExcludes (v w : String) : Bool := false
def isEntails (v w : String) : Bool := v ≠ w

end App
