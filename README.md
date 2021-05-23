# velev09hcp

## Outline

  This program is an implementation of the SAT encoding method of
  the following paper:

  Miroslav N. Velev and Ping Gao, "Efficient SAT Techniques for
  Relative Encoding of Permutations", Australasian Conference on
  Artificial Intelligence, pp. 517--527, 2009.

## Files

  - README : this file
  - velev09.pl : main program

## Requirements 

  - perl (we checked this program works on 5.12.3. But it probably
    works on other Perl 5.)
  - minisat (http://minisat.se) with output file, or other SAT solvers generates a model in competition format.

## Before Running
  
  please edit line 11 of velev09.pl according to the path to minisat

## Usage

``` bash
$ ./velev09.pl <Input File>
```

## Options

-keep          this option keeps encoded *.cnf file and SAT solution
               file *.cnf

-solvert=<solver path.> set sat solver

## Example

``` bash
$ ./velev09.pl -keep -solver /hoge/minisat myciel5.col
```
