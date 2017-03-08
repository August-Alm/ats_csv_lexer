# ats_csv_lexer
A program to parse CSV files, written in ATS (ATS2). The code makes extensive use of laziness and linear types.

Compilation with 

  $ patscc -O2 -flto -DATS_MEMALLOC_GCBDW -lgc -o csv_lexer csv_lexer.dats 

ought to generate good behaviour, though other flags will also work, such as: 

  $ patscc -DATS_MEMALLOC_LIBC -o csv_lexer csv_lexer.dats 

The program parses CSV data conforming to the RFC 4180 standard. The algorithm uses the same over-arching logic as the Haskell package "lazy-csv" but makes significant use of features unique to ATS. In particular, it extensively uses linear types to almost entirely eliminate the need for garbage collection. It does put strain on the stack space though. If the size of a field (input string between two comma signs) exceeds 52119 bytes, then the program will segfault when run under Linux' standard stack size (8192 times 1024 bytes). It does handle close to arbitrarily large files however, only the size of the field is a practical issue and 5 kbyte field size should be enough for virtually all applications. (That's five thousand characters per field!)
