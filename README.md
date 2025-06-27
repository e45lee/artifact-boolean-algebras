# Introduction
This artifact contains both the formalized proof of F<:B and F<:BE as discussed
in the paper and the modified Flix compiler used in the evaluation.

The proof consists of two calculi:
- F<:B, formalized in ([proofs/Base](proofs/Base)), consisting of an qualifier calculus
  based on an arbritary boolean algebra with uninterpreted qualifiers.
- F<:BE, formalized in ([proofs/EffectExclusion](proofs/EffectExclusion)), consisting
  of a calculus where the qualifiers denote potential effects functions may
  perform.

These proofs are based on the [POPLMark 08
tutorial](https://github.com/plclub/metalib) by Aydemir et. al. and the proof of
[Qualifying System F<:](https://github.com/e45lee/qualifying-fsub-proofs) by Lee
et. al.

The claims of the evaluation section is all expressed in the tables (1-4) and
all except the first can be replicated as described below. The first table is a
snapshot in time of online data and cannot as such be replicated meaningfully.

This evaluation portion of this artifact consists of:
- .devcontainer/
  - This folder has a configuration for opening the container in VSCode.
- evaluation/flix-compiler-source/
  - This folder contains the source code of the modified Flix compiler,
    described and used in the paper. The compiler is not documented specifically
    in this artifact but has its existing documentation.
- evaluation/library../
  - These folders are used for Table 3 and is explained in Step by Step
    Instructions.
- evaluation/flix.flix-1.40.0.vsix
  - This is the VSCode extension for Flix, used if opening the container in
    VSCode.
- evaluation/flix.jar
  - This is the built jar of flix-compiler-source. The `flix` command is just
    shorthand for `java -jar flix.jar`.

# Hardware Dependencies
Since the artifact is contained within a Docker image, the only hardware requirements is a computer running on either AMD64 or on an modern 64-bit ARM implementation.

# Getting Started Guide
The Docker image containing both the Flix installation and the precompiled proofs can be found within the artifact, 
and can be loaded by running the appropriate command for your architecture:
```
docker load --input artifact-boolean-algebras-x86.tar # amd64

docker load --input artifact-boolean-algebras-arm64.tar # arm64
```

Alternatively, one can download the Docker image directly from GitHub directly by running:
```
docker pull ghcr.io/e45lee/artifact-boolean-algebras
docker image tag ghcr.io/e45lee/artifact-boolean-algebras artifact-boolean-algebras
```

Once the image has been loaded or downloaded, one can run the image by running:
```
docker run -it artifact-boolean-algebras
```
to enter the container terminal. It holds a copy of this README.md for convenience.

To see that the proofs are correct, you can rebuild the proofs by:
```
cd proofs
make clean
make
```

Flix is invoked via the `flix` command. If you just want to see it run, use
`flix check --Xsummary --Xsubeffecting se-def,se-ins,se-lam` which will type
check the standard library with all subeffecting options and output the library
summary table of the paper.

The meaning of the subeffecting options are explained in the paper
- `se-def`: adds abstraction-site subeffecting to top-level functions.
- `se-ins`: adds abstraction-site subeffecting to instance functions.
- `se-lam`: adds abstraction-site subeffecting to lambdas and nested defs.

# Step by Step Instructions

## Replication -- Proofs

### Definitions
Definitions for each calculus can be found in `Fsub_LetSum_Definitions.v` in
each respective folder.  The proofs are presented in a locally nameless style, following the POPLMark 08 tutorial.

### Soundness Theorems / Proofs
Soundness (progress and preservation proofs) for each calculus can be found in
`Fsub_LetSum_Soundness.v` in each respective folder.
These theorems are found under `Lemma progress` and `Lemma preservation` respectively.

### Extracting the pre-built proofs and proof documentation
While the artifact contains the sources of the Rocq files and the documentation
associated with the Coq proofs as well, the Docker image contains a pre-built copy of both the Rocq proofs and documentation under `/workspace/proofs`.


To extract the pre-built proofs and documentation (into
a folder called `proofs`), run:
```
docker run artifact-boolean-algebras tar c proofs | tar x
```

In addition, the Coq documentation can be found online at (hopefully soon!):
<https://e45lee.github.io/artifact-boolean-algebras/toc.html>

## Replication -- Flix
We will use `flix` commands to replicate the tables of the paper.

Running `flix` will always say
```
No `flix.toml`. Will load source files from `*.flix`, `src/**`, and `test/**`.
```
since we don't use a `flix.toml` file, this is okay.

The numbers found here slightly differs to the paper in some ways. These new
numbers will be reflected in the revised paper and will then correspond exactly.

### Table 1 (page 17)
This table is a snapshot in time of publicly hosted data so it cannot be
replicated.

### Table 2 (page 18)
```
flix check --Xsummary --Xsubeffecting se-def,se-ins,se-lam
```
This:
- type checks the standard library (`check`), and
- produces the library summary (`--Xsummary`) with
- all three subeffecting sites enabled `--Xsubeffecting se-def,se-ins,se-lam`.

The output should look like this:
```
|               Module |  Lines |  Defs |  Pure | Effectful |  Poly | checked_ecast | Baseline EVars | SE-Def EVars | SE-Ins EVars | SE-Lam EVars |
| -------------------- | ------ | ----- | ----- | --------- | ----- | ------------- | -------------- | ------------ | ------------ | ------------ |
|         Adaptor.flix |    238 |    21 |     6 |         5 |    10 |             0 |            137 |          +15 |           +0 |          +22 |
|     Applicative.flix |    185 |    14 |     8 |         0 |     6 |             0 |             42 |           +6 |           +0 |          +20 |
|           Array.flix |  1,689 |   138 |     5 |         0 |   133 |             1 |          1,702 |         +130 |           +3 |          +92 |
|      BigDecimal.flix |    213 |    22 |    22 |         0 |     0 |             0 |             49 |           +0 |           +0 |           +0 |
|          BigInt.flix |    393 |    37 |    37 |         0 |     0 |             0 |            117 |           +0 |           +0 |          +10 |
|           Chain.flix |    975 |   112 |    59 |         2 |    51 |             1 |            658 |          +36 |          +17 |          +54 |
|           Chalk.flix |    560 |    55 |    55 |         0 |     0 |             0 |            295 |           +0 |           +0 |           +7 |
|            Char.flix |    243 |    31 |    31 |         0 |     0 |             0 |             38 |           +0 |           +0 |           +0 |
|       CodePoint.flix |    306 |    33 |    33 |         0 |     0 |             0 |             72 |           +0 |           +0 |           +0 |
|       Concurrent/... |    727 |    31 |     3 |        28 |     0 |             0 |            151 |          +28 |           +0 |           +6 |
|       DelayList.flix |  1,346 |   110 |    55 |         1 |    54 |             3 |            943 |          +42 |          +13 |          +78 |
|        DelayMap.flix |    889 |    81 |    37 |         1 |    43 |             0 |            588 |          +38 |           +6 |         +177 |
|     Environment.flix |    137 |    16 |    16 |         0 |     0 |             0 |             31 |           +0 |           +0 |           +0 |
|              Eq.flix |    242 |    37 |    37 |         0 |     0 |             0 |            129 |           +0 |           +0 |           +0 |
|            File.flix |    452 |    37 |     1 |        29 |     7 |             0 |            113 |          +35 |           +1 |          +34 |
|           Files.flix |    943 |    47 |     1 |        35 |    11 |             4 |            496 |          +46 |           +0 |          +56 |
|         Fixpoint/... |  3,243 |   152 |   123 |         0 |    29 |             0 |          2,401 |          +29 |           +0 |         +225 |
|         Float32.flix |    339 |    37 |    37 |         0 |     0 |             0 |            118 |           +0 |           +0 |           +0 |
|         Float64.flix |    373 |    39 |    39 |         0 |     0 |             0 |            117 |           +0 |           +0 |           +0 |
|        Foldable.flix |    396 |    46 |     0 |         0 |    46 |             2 |            264 |          +46 |           +0 |          +74 |
|          GetOpt.flix |    421 |    26 |    24 |         0 |     2 |             0 |            188 |           +2 |           +0 |          +19 |
|           Graph.flix |    558 |    29 |     5 |         0 |    24 |             0 |            261 |          +24 |           +0 |          +13 |
|           Group.flix |    165 |    29 |    29 |         0 |     0 |             0 |             74 |           +0 |           +0 |           +0 |
|            Hash.flix |    171 |    23 |    23 |         0 |     0 |             0 |            112 |           +0 |           +0 |           +0 |
|        Identity.flix |    133 |    20 |    10 |         0 |    10 |             1 |             55 |           +0 |          +10 |           +1 |
|           Int16.flix |    446 |    54 |    54 |         0 |     0 |             0 |            172 |           +0 |           +0 |           +0 |
|           Int32.flix |    480 |    56 |    56 |         0 |     0 |             0 |            171 |           +0 |           +0 |           +1 |
|           Int64.flix |    494 |    57 |    57 |         0 |     0 |             0 |            188 |           +0 |           +0 |           +1 |
|            Int8.flix |    419 |    52 |    52 |         0 |     0 |             0 |            159 |           +0 |           +0 |           +0 |
|        Iterator.flix |    759 |    50 |    12 |         0 |    38 |             4 |            692 |          +38 |           +0 |          +73 |
|     JoinLattice.flix |    212 |    14 |    14 |         0 |     0 |             0 |             59 |           +0 |           +0 |           +0 |
|            List.flix |  1,433 |   155 |    89 |         2 |    64 |             6 |            995 |          +49 |          +17 |         +128 |
|             Map.flix |    984 |   121 |    50 |         2 |    69 |             0 |            655 |          +58 |          +13 |         +174 |
|     MeetLattice.flix |    213 |    14 |    14 |         0 |     0 |             0 |             59 |           +0 |           +0 |           +0 |
|        MultiMap.flix |    568 |    71 |    31 |         1 |    39 |             0 |            412 |          +33 |           +7 |         +122 |
|        MutDeque.flix |    446 |    41 |     5 |         0 |    36 |             0 |            557 |          +35 |           +1 |          +18 |
| MutDisjointSets.flix |    178 |    10 |     1 |         0 |     9 |             0 |            112 |           +9 |           +0 |           +5 |
|         MutList.flix |    936 |    82 |     1 |         0 |    81 |             0 |          1,068 |          +78 |           +3 |          +51 |
|          MutMap.flix |    679 |    78 |     0 |         0 |    78 |             3 |            555 |          +75 |           +3 |          +22 |
|        MutQueue.flix |    225 |    18 |     0 |         0 |    18 |             0 |            257 |          +17 |           +1 |           +8 |
|          MutSet.flix |    436 |    50 |     0 |         0 |    50 |             1 |            362 |          +49 |           +1 |           +7 |
|             Nec.flix |  1,034 |   129 |    63 |         2 |    64 |             8 |            919 |          +42 |          +24 |          +95 |
|             Nel.flix |    712 |   110 |    54 |         2 |    54 |             1 |            426 |          +32 |          +24 |          +25 |
|          Option.flix |    585 |    78 |    33 |         0 |    45 |             2 |            242 |          +28 |          +17 |          +16 |
|           Order.flix |    653 |    71 |    71 |         0 |     0 |             0 |            263 |           +0 |           +0 |           +0 |
|    PartialOrder.flix |    197 |    14 |    14 |         0 |     0 |             0 |             56 |           +0 |           +0 |           +0 |
|         Prelude.flix |    247 |    18 |    12 |         2 |     4 |             0 |             59 |           +6 |           +0 |           +3 |
|    RedBlackTree.flix |  1,003 |    80 |    41 |         0 |    39 |             3 |            722 |          +28 |          +11 |          +95 |
|       Reducible.flix |    296 |    38 |    21 |         0 |    17 |             2 |            197 |          +17 |           +0 |          +64 |
|           Regex.flix |    716 |    55 |    42 |         0 |    13 |             0 |            457 |          +13 |           +0 |          +16 |
|          Result.flix |    443 |    48 |    17 |         0 |    31 |             2 |            183 |          +28 |           +3 |          +16 |
|       SemiGroup.flix |    169 |    25 |    25 |         0 |     0 |             0 |             68 |           +0 |           +0 |           +0 |
|             Set.flix |    642 |    83 |    43 |         1 |    39 |             0 |            465 |          +30 |          +10 |         +103 |
|          String.flix |  1,377 |   121 |   100 |         0 |    21 |             0 |            783 |          +21 |           +0 |          +53 |
|   StringBuilder.flix |    147 |    17 |     0 |         0 |    17 |             0 |            101 |          +17 |           +0 |           +6 |
|             Time/... |    176 |    15 |    10 |         5 |     0 |             0 |             21 |           +5 |           +0 |           +0 |
|        ToString.flix |    186 |    27 |    27 |         0 |     0 |             0 |            129 |           +0 |           +0 |           +0 |
|      Validation.flix |    294 |    32 |    14 |         0 |    18 |             0 |            140 |          +16 |           +2 |          +20 |
|          Vector.flix |  1,523 |   158 |    87 |         3 |    68 |             3 |          1,162 |          +53 |          +18 |         +104 |
|                  ... |    ... |   ... |   ... |       ... |   ... |           ... |            ... |          ... |          ... |          ... |
|               Totals | 37,551 | 3,543 | 2,027 |       133 | 1,383 |            47 |         22,871 |       +1,311 |         +205 |       +2,142 |
```

There are three differences from the paper:
- We had a mistake where lambdas in the form of nested defs (`def` inside `def`)
  where not counted. Only anonymous lambdas were counted (`x -> ..`). This means
  that the counts in SE-Lam has increased (total was 1816, now 2142).
- We had a mistake where default functions in traits where double counted. This
  means that the counts in SE-Def has decreased slightly (total was 1389, now
  1311).
- The Baseline column is computed from the total variables, so because the two
  other columns have changed, the base line have changed accordingly (total was
  23119, now 22871).

### Table 3 (page 20)
There are four folders containing copies of the Flix standard library:
- library: This folder contains the baseline standard library, used by the
  compiler. The exact commit this is taken from is
  https://github.com/flix/flix/tree/76b7eb24669cfcb7b42f2155ab6da8fd19fa8bfe
- library-all-casts-removed: This folder has the library, where the 47
  `checked_ecast` has been removed.
- library-ins-casts-removed: This folder has the library, where the 1
  `checked_ecast` that could be removed by SE-Ins has been removed.
- library-lam-casts-removed: This folder has the library, where the 46
  `checked_ecast` that could be removed by SE-Lam has been removed.


The count of 47 casts in the library can be verified by
```
grep -r "checked_ecast" library
```
or with automatic counting by
```
grep -o -r "checked_ecast" library | wc -l
```
which should output `47`.


The differences of the folders can be observed with
```
diff -r <library1> <library2>
```
e.g. `diff -r library library-all-casts-removed` will list the 47 casts removed.


The compilation of these can be verified by
```
cd library
flix check --Xlib nix
cd ..

cd library-all-casts-removed
flix check --Xlib nix --Xsubeffecting se-ins,se-lam
cd ..

cd library-ins-casts-removed
flix check --Xlib nix --Xsubeffecting se-ins
cd ..

cd library-lam-casts-removed
flix check --Xlib nix --Xsubeffecting se-lam
cd ..
```

`--Xlib nix` removes the packaged standard library, and uses the library of the
folder.

These listed commands use the minimum required subeffecting, as shown in the
paper, but you can also reduce the subeffecting options and see that it does not
type check (it will print some type errors). For the valid options, the `check`
call should just return with no errors.

### Table 4 (page 21)
The two effect variables columns are based on Table 2, see above. The variable
count of a row, is the number of total variables in Table 2 plus the total of
the row-site added on top. E.g for Def, based on the table above, it is the
total of column "Baseline EVars" (22,871), plus the total of column "SE-Def
EVars" (1,311), which is 24,182. This is an increase of
`100 * (24,182/22,871 - 1) = 5.7`

Assuming that table 2 is replicated, the Effect variables columns are now:

|          | Paper                | Artifact
|          | Variables | Increase | Variables | Increase |
| -------- | --------- | -------- | --------- | -------- |
| Baseline |    23,119 |        - |    22,871 |        - |
| Def      |    24,508 |     6.0% |    24,182 |     5.7% |
| Ins      |    23,324 |     0.9% |    23,076 |     0.9% |
| Lam      |    24,935 |     7.9% |    25,013 |     9.4% |

The difference to the paper is slight, not invaliding the claims of the paper.

The throughput is the median reported by
```
flix Xperf --frontend --par --n 300 --Xsubeffecting <subeffecting options>
```
This:
- runs performance benchmarking (`Xperf`) of the
- frontend of the compiler (the part used by editors) (`--frontend`).
- It will uses all available cores (`--par`) and
- do 300 runs (`--n 300`) with
- the given subeffecting options (`--Xsubeffecting <subeffecting options>`).

The rows can be replicated with this (time consuming) command
```
flix Xperf --frontend --par --n 250 &&
flix Xperf --frontend --par --n 250 --Xsubeffecting se-def &&
flix Xperf --frontend --par --n 250 --Xsubeffecting se-ins &&
flix Xperf --frontend --par --n 250 --Xsubeffecting se-lam
```
Each `Xperf` command will report progress on each run `Run x/250` and then at
the end it will output something like
```
~~~~ Flix Compiler Performance ~~~~

Throughput (best): 21,965 lines/sec (with 12 threads.)

  min: 10,866, max: 21,965, avg: 16,415, median: 21,965

Finished 250 iterations on 67,181 lines of code in 453 seconds.
```
where the median (here `21,965`) is the number used in the paper.

We found 250 to be a good number to reach stable performance (JVM JIT wil warm
up and become faster), but you can choose the number of runs freely.

The slowdown factor is computed by `baseline/throughput`.

The results here will probably be slower than than the paper, assuming an
average laptop, but the slowdown factor of the three options should be similar
to the paper. (~1.05x for se-def, ~1.01x for se-ins, and ~1.18x for se-lam).

The claim of the paper is that the slowdown of the subeffecting options are
moderate and are acceptable, so as long as the slowdown is not worse than
listed, the claim remains valid.

## Replication -- Rebuilding the Artifact
While not necessary to check the proofs nor to run Flix, the Docker images for this artifact can be rebuilt by running the 
`./rebuild-artifact` script located at the root of the artifact from outside Docker.  Docker BuildX will need to be installed
to do so.

## Using Flix and VSCode
You can play around with Flix and the subeffecting via the command line or
VSCode via the docker container extension.

### REPL
To use the Flix repl, simply call `flix` with the subeffecting options of
interest. The following shows an example.

```
$ flix --Xsubeffecting se-def
No `flix.toml`. Will load source files from `*.flix`, `src/**`, and `test/**`.
     __   _   _
    / _| | | (_)            Welcome to Flix 0.52.0
   | |_  | |  _  __  __
   |  _| | | | | \ \/ /     Enter an expression to have it evaluated.
   | |   | | | |  >  <      Type ':help' for more information.
   |_|   |_| |_| /_/\_\     Type ':quit' or press 'ctrl + d' to exit.
flix> def inc(x: Int32): Int32 \ IO = x
Ok.
flix> def inc2(): Int32 -> Int32 \ IO = x -> x + 1
-- Type Error -------------------------------------------------- $2

>> Mismatched Pure and Effectful Functions.

1 | def inc2(): Int32 -> Int32 \ IO = x -> x + 1
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    mismatched pure and effectful functions.

Type One: Int32 -> Int32 \ IO
Type Two: Int32 -> Int32

Error: Declaration ignored due to previous error(s).
flix> :q
```

Here you can see that `se-def` allows subeffecting on the def but not on the
lambda.

### Run a file
```
echo "def main(): Int32 \ IO = 32" > test.flix
flix test.flix --Xsubeffecting se-def
```
This should print 32, and you can edit the `test.flix` file as you please.

### VSCode
You can use VSCode on your own computer to hook into the docker container and
have the full IDE experience.

- Download VSCode https://code.visualstudio.com/download
- Open a new window.
- Open extensions.
- Install "Dev Containers" by Microsoft.
- Open the artifact folder in VSCode, the one that contains .devcontainer/
- Open up the VSCode search (at the top of the window).
- Search ">Dev Containers: Reopen in Container" and choose that option.
- If this fails, make sure you have done the Getting Started Guide and has
  created a container.
- Now you should see the artifact folder open.
- Right-click on the .vsix file and select install extension.
- Create a file "test.flix" and begin typing, you should see the highlighting
  and error reporting.

The subeffecting settings can be changed in the extension settings under
"additional flix compiler arguments" and using `--Xsubeffecting se-lam` fx.

# Reusability Guide

## Proofs
In general, the base calculi (stored in [proofs/Base](proofs/Base)) and can be reused
to serve as the basis of a soundness proof for a specific instantiation of a
qualifier calculus to concrete qualifiers and interpretations. In particular,
to construct our proofs of soundness for our effect-exclusion derived calculus
we started from our base calculus proof and extended it with the new terms and
reduction rules -- features -- present in each extension, taking care to assign
meaningful and reasonable interpretations of qualifiers as well, as one would do
on paper as well.

## Compiler
The Flix programming language is fully open source and extensively documented.
The compiler itself is in `flix-compiler-source/` folder but supportive material
exists externally. You can modify the compiler in anyway you want and build it
with `./gradlew build` in the `flix-compiler-source/` folder. Running build
might take upwards of 5 minutes.

The main website is:

    https://flix.dev/

The main GitHub repository contains the source code (similar to
`flix-compiler-source/`):

    https://github.com/flix/flix

There is an online playground with extensive examples:

    https://play.flix.dev/

There is extensive online documentation (more than 200 pages):

    https://doc.flix.dev/

A researcher that wants to build on our work can obtain everything they need
from the GitHub repository. The build instructions are here:

    `flix-compiler-source/docs/BUILD.md`