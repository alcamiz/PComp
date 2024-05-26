<div align="center">

# PComp

A minimal pascal compiler written with flex / yacc generating code for x86 architectures.

Written in 2022 for CS375

</div>

## Building

Run the following:

```
git clone https://github.com/alcamiz/PComp.git
cd PComp
make compiler
```

## Executing

Compile some pascal code:

```
./compiler INFILE [OUTFILE]
```

Run generated code:

```
gcc driver.c code.s -lm
a.out
```
