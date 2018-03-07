module GraphBackward where
import Data.Array
import Data.List
import SuccinctBackward
import Utility

type Vertex = Int
type Table a = Array Vertex a
type Graph e = Table [(e, Vertex)]
type Bounds = (Vertex, Vertex)
type Edge e = (Vertex, e, Vertex)

type Labeling a = Vertex -> a
data LabGraph n e = LabGraph (Graph e) (Labeling n)

-- getVertices :: Graph e -> [Vertex]
-- getVertices g = [ v | (e, v) <- g]

vertices (LabGraph gr _) = indices gr
labels (LabGraph gr l) = map l (indices gr)

-- | Build a graph from a list of edges.
buildG :: Bounds -> [Edge e] -> Graph e
buildG bounds0 edges0 = accumArray (flip (:)) [] bounds0 [(v, (l,w)) | (v,l,w) <- edges0]

-- | The graph obtained by reversing all edges.
transposeG  :: Graph e -> Graph e
transposeG g = buildG (bounds g) (reverseE g)
 
reverseE    :: Graph e -> [Edge e]
reverseE g   = [ (w, l, v) | (v, l, w) <- edges g ]

showGraphViz (LabGraph gr lab) tyIndices =
  "digraph name{\n" ++
  "layout=dot;\n" ++
  "splines=true;\n" ++ 
  "margin=\"0.5,0.5\";\n" ++
  "fontsize=16;\n" ++
  "dpi=250;\n"++
  "concentrate=True;\n" ++
  "rankdir=BT;\n" ++
  "ratio=fill;\n" ++
  "size=\"8.5,11!\";\n" ++
  "node  [style=\"rounded,filled,bold\", shape=box, width=2, fontsize=24];\n"++
  "edge [fontsize=24]\n"++
  (concatMap showNode $ indices gr) ++
  (concatMap showEdge $ edges gr) ++
  "}\n"
  where showEdge (from, t, to) = let fromName = (getTypeName tyIndices from)
                                     toName =  (getTypeName tyIndices to)
                                 in (if fromName == "\"\"" then "done"++(show from) else fromName) ++ 
                                    " -> " ++
                                    (if toName == "\"\"" then "done"++(show to) else toName)++
                                    " [label = " ++ show t ++ ", fontname=\"Segeo UI\",fontsize=20;];\n"
        showNode v = let name = (getTypeName tyIndices v) 
                     in if name == "\"\"" 
                          then "done"++ (show v) ++ "[shape=circle,width=0.25,fillcolor=\"#33a02c\", style=filled, label = \"\",fontname=\"Segeo UI\",fontsize=20;];\n" 
                          else name ++ " [label = " ++ (lab v) ++ ", fontname=\"Segeo UI\",fontsize=20;];\n"

edges :: Graph e -> [Edge e]
edges g = [ (v, l, w) | v <- indices g, (l, w) <- g!v]

generateEdges :: [(STy, String, STy)] -> [(Int, STy)] -> [Edge String]
generateEdges tys tyIndices = map (\(from,name,to)->((getTypeIndex tyIndices from), name, (getTypeIndex tyIndices to))) tys