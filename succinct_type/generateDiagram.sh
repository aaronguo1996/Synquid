stack runhaskell $1 $2
dot -Tpng $2 -o $2.png
dot -Tpng $2_pruned -o $2_pruned.png
