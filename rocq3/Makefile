# Build the EqCat development (Coq 8.15).
FILES = Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect Adequacy Examples Presented EckmannHilton Derived Functor Inverse
all: $(FILES:=.vo)
%.vo: %.v
	coqc -q -R . EqCat $<
Axioms.vo: Syntax.vo
Meta.vo: Axioms.vo
NormalForm.vo: Meta.vo
Model.vo: NormalForm.vo
FreeModel.vo: Model.vo
Decidable.vo: FreeModel.vo
Reflect.vo: Decidable.vo
Adequacy.vo: Reflect.vo
Examples.vo: Adequacy.vo
Presented.vo: Syntax.vo
EckmannHilton.vo: Presented.vo
Derived.vo: Reflect.vo
Functor.vo: Adequacy.vo
Inverse.vo: Functor.vo
audit: Examples.vo
	@grep -n "^[[:space:]]*Admitted\.\|^[[:space:]]*admit\." *.v || echo "no admits"
# coqdoc pages that the paper's \rocq{File}{Anchor} links point to.
html: all
	mkdir -p html
	coqdoc --html --utf8 --toc -R . EqCat -d html $(FILES:=.v)
clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux
.PHONY: all audit html clean
