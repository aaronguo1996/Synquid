stack runhaskell Main.hs > diagram.dig
dot -Tpng diagram.dig -o $1