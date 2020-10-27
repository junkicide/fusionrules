[![Travis build Status](https://travis-ci.org/gap-system/gap.svg?branch=master)](https://travis-ci.org/gap-system/gap)
[![AppVeyor build Status](https://ci.appveyor.com/api/projects/status/github/gap-system/gap?branch=master&svg=true)](https://ci.appveyor.com/project/gap-system/gap)
[![Code Coverage](https://codecov.io/github/gap-system/gap/coverage.svg?branch=master&token=)](https://codecov.io/gh/gap-system/gap)
[![Coverage Status](https://coveralls.io/repos/github/gap-system/gap/badge.svg)](https://coveralls.io/github/gap-system/gap)

# fusionrules

This is a GAP program to compute fusion rules for group-theoretical fusion categories. The theory explaining the algorithm used is explained in chapter 4 of my PhD thesis, which can be found in the [thesis](https://github.com/junkicide/thesis/) repository.
## Instructions

Requires
- GAP 4.11.0
- the hapcocyclic package

After having downloaded all the files above, navigate to the directory and launch GAP from there. Load the launch.g file as follows

```
Read("launch.g");
```


Suppose we want to compute the fusion rules for all group theoretical categories (G, H, omega, 1) for a fixed G and all possible H and omega.

```
G:=SmallGroup(8, 3);
fusion(G);
```

This will print the fusion rules for all possible group theoretical fusion categories with G the dihedral group of size 8. 

Suppose we have a specific G and H, then we can do the following
```
G:=SmallGroup(8, 3);
H:= SubgroupsUptoAutomorphism(G)[1];
fusion(G, H);
```
This computes fusion rules for all group theoretical categories with that specific group and subgroup.

Further if we choose a specific cocycle
```
coho:=GHCoho(G, H, 3)[2];
fusion(G, H, coho);
```
This will print the fusion rules for the group theoretical data (G, H, coho, 1).

In case there are issues, you may try to edit the launch.g file so that the relative paths to the files in question are correct. In case the problem still persists, please do get in touch! Suggestions and improvements are welcome.
