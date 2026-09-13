# Build the EqCat development (Coq 8.15).
FILES = Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect Adequacy Examples
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
audit: Examples.vo
	@grep -n "^[[:space:]]*Admitted\.\|^[[:space:]]*admit\." *.v || echo "no admits"
clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux
.PHONY: all audit clean
