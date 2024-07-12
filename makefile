# Makefile for OCaml project

# List of source files
SOURCES = ast.ml utilities.ml eval.ml type_checking.ml test.ml

# List of compiled object files
OBJECTS = $(SOURCES:.ml=.cmo)

# The final executable
EXECUTABLE = project

# Default target
all: $(EXECUTABLE)

# Rule to compile the final executable
$(EXECUTABLE): $(OBJECTS)
	ocamlc -o $@ $^

# Pattern rule to compile .ml files to .cmo and .cmi
%.cmo: %.ml
	ocamlc -c $<

# Clean target to remove compiled files
clean:
	rm -f *.cmi *.cmo 

# Phony targets
.PHONY: all clean
