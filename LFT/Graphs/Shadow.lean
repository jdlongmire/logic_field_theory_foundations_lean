import LFT.Graphs
import LFT.Graphs.RichGraph

/-!
Provide an optional "shadow" mapping from your `Graph` to a `RichGraph`
that carries typed edges. If present, we’ll use it for counts.
-/

namespace LFT
namespace Graphs

/-- App-layer hook: supply a RichGraph shadow for a core Graph. -/
class GraphHasRichShadow (α : Type) where
  toRich : α → Option RichGraph

/-- Default: no shadow provided. Your app can override with a real instance. -/
instance : GraphHasRichShadow LFT.Graph where
  toRich _ := none

end Graphs
end LFT
