[![Travis build Status](https://travis-ci.org/gap-system/gap.svg?branch=master)](https://travis-ci.org/gap-system/gap)
[![AppVeyor build Status](https://ci.appveyor.com/api/projects/status/github/gap-system/gap?branch=master&svg=true)](https://ci.appveyor.com/project/gap-system/gap)
[![Code Coverage](https://codecov.io/github/gap-system/gap/coverage.svg?branch=master&token=)](https://codecov.io/gh/gap-system/gap)
[![Coverage Status](https://coveralls.io/repos/github/gap-system/gap/badge.svg)](https://coveralls.io/github/gap-system/gap)

# fusionrules

This is a GAP program to compute fusion rules for group-theoretical fusion categories. The theory explaining the algorithms used will be available on the arxiv soon enough. 

## Instructions

Requires
- GAP 4.11.0
- the hapcocyclic package

After having downloaded all the files above, navigate to the directory and launch GAP from there. Load the launch.g file as follows

```console
Read("launch.g");
```
This may throw an error, in which case repeating the same command works.

Suppose we want to compute the fusion rules for all group theoretical categories (G, H, omega, 1) for a fixed G and all possible H and omega.

```console
G:=SmallGroup(8, 3);
fusion(G);
```

This will print the fusion rules for all possible group theoretical fusion categories with G the dihedral group of size 8. For each group theoretical category it will also write the dimensions and the fusion rules to a file.

Suppose we have a specific G and H, then we can do the following


```console
G:=SmallGroup(8, 3);
H:= SubgroupsUptoAutomorphism(G)[1];
coho:=GHCoho(G, H, 3)[2];
GTCat(G, H, coho);
```
This will print the fusion rules for the group theoretical data (G, H, coho, 1).

Please get in touch if you have any questions or want to report a bug.
