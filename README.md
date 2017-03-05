# ats_csv_lexer
A program to parse CSV files, written in ATS (ATS2). The program works but has stack allocation problems causing it to segfault on larger inputs.

Compilation with 

  $ patscc -O2 -flto -DATS_MEMALLOC_GCBDW -lgc -o csv_lexer csv_lexer.dats 

ought to generate good behaviour, though other flags will also work, such as: 

  $ patscc -DATS_MEMALLOC_LIBC -o csv_lexer csv_lexer.dats 
