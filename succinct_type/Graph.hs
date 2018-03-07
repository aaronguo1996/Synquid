module Graph where
import Data.Array
import Data.List
import SuccinctForward
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
  "digraph name {\n" ++
  "rankdir=LR;\n" ++
  (concatMap showNode $ indices gr) ++
  (concatMap showEdge $ edges gr) ++
  "}\n"
  where showEdge (from, t, to) = (getTypeName tyIndices from) ++ " -> " ++ (getTypeName tyIndices to) ++
                                 " [label = " ++ show t ++ "];\n"
        showNode v = (getTypeName tyIndices v) ++ " [label = " ++ (show $ lab v) ++ "];\n"

edges :: Graph e -> [Edge e]
edges g = [ (v, l, w) | v <- indices g, (l, w) <- g!v]

generateEdges :: (String, SuccinctType) -> [(SuccinctType, Int)] -> [Edge String]
generateEdges (name, ty) tyIndices = case ty of
    SuccSgl t -> []
    SuccCons t -> []
    SuccCom tyLst -> let tys = foldl (\acc t -> removeDups ((getTypes t) ++ acc) []) [] tyLst
                     in map (\t -> addEdge t ty "") tys
    SuccVar names tys -> []
    SuccFun tyLst retTy | length tyLst == 0 -> let SuccSgl tt = retTy in [addEdge retTy (SuccCons tt) "rooted_value"]
                        | length tyLst == 1 -> let tys = foldl (\acc t -> removeDups ((getTypes t) ++ acc) []) [] tyLst
                                               in [addEdge (head tys) retTy name]
                        | otherwise -> let tys = foldl (\acc t -> removeDups ((getTypes t) ++ acc) []) [] tyLst
                                       in [addEdge (SuccCom tys) retTy name]
  where
    addEdge src dst name = (getTypeIdx tyIndices src, name, getTypeIdx tyIndices dst)
