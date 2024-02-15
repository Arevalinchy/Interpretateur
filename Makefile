ast_interpreter.out: compiler/*/*.ml compiler/*/*.mli
	rm -rf ast_interpreter.out
	dune build
	ln -s _build/default/compiler/bin_ast_interpreter/main.exe ast_interpreter.out

.PHONY: clean
clean:
	rm -rf ast_interpreter.out doc.html
	dune clean

.PHONY: doc
doc: doc.html

doc.html:
	rm -f doc.html
	dune build @doc
	ln -s _build/default/_doc/_html/index.html doc.html