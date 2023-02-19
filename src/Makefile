JanssonDimensions2023.pdf: JanssonDimensions2023.tex
	latexmk -pdf JanssonDimensions2023

JanssonDimensions2023.tex: JanssonDimensions2023.lagda.tex
	lhs2TeX --agda --set="allCode=False" JanssonDimensions2023.lagda.tex > JanssonDimensions2023.tex

code: JanssonDimensions2023_code.agda

JanssonDimensions2023_code.agda: JanssonDimensions2023.lagda.tex
	lhs2TeX --set="allCode=True" --agda --code  JanssonDimensions2023.lagda.tex \
            > JanssonDimensions2023_code.agda
