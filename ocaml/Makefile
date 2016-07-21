OCAMLC = ocamlfind ocamlc -package stringext,js_of_ocaml.syntax,js_of_ocaml.deriving.syntax,js_of_ocaml.deriving,deriving -syntax camlp4o -package js_of_ocaml  

OBJS = sj.cmo main.cmo

NAME = sj

JSC = js_of_ocaml  --disable genprim 


all: $(NAME).html

$(NAME).html: $(NAME).js
	./embed-js

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmo: %.ml %.cmi
	$(OCAMLC) -c $<

$(NAME).byte: $(OBJS)
	$(OCAMLC) -linkpkg -o $@ $^

clean:
	rm -f *.cmo *.cmi *.cmx $(NAME).byte $(NAME).js *.o

$(NAME).js: $(NAME).byte
	$(JSC) $<
