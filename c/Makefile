# Snel C99 build. `make` produces ./snel.
CC ?= cc
CFLAGS ?= -std=c99 -O2 -Wall -Wextra -Wno-unused-parameter
SRC = value.c ast.c lex.c parse.c print.c ops.c eval.c wire.c io.c check.c interop.c lsp.c main.c
OBJ = $(SRC:.c=.o)

snel: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $(OBJ) -lm

%.o: %.c snel.h
	$(CC) $(CFLAGS) -c -o $@ $<

# reformat the port with clang-format (config in ../.clang-format)
format:
	clang-format -i *.c *.h

clean:
	rm -f $(OBJ) snel

.PHONY: clean format
