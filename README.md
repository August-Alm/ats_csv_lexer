# ats_csv_lexer
A program to parse CSV files, written in ATS (ATS2). The code makes extensive use of laziness and linear types.

Compilation with 

  $ patscc -O2 -flto -DATS_MEMALLOC_GCBDW -lgc -o csv_lexer csv_lexer.dats 

ought to generate good behaviour, though other flags will also work, such as: 

  $ patscc -DATS_MEMALLOC_LIBC -o csv_lexer csv_lexer.dats 
