{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}


main = writeFile "foo.tex" doc2

doc2 = []

doc = beginning ++ middle ++ end

beginning = "\\documentclass{article}\\title{Cut-elimination output}\\date{}\\begin{document}\\maketitle{}"

middle = ""

end = "\\end{document}"





