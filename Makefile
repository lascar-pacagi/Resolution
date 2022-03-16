all:
	ocamlbuild -use-ocamlfind -use-menhir -menhir "menhir --explain --dump" -pkgs str main.native
	mv main.native solve

clean:
	ocamlbuild -clean
	rm -f solve
