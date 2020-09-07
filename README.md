## Implementation

Please see [the Jupyter notebook](https://github.com/anonymous-ewok/anonymous-ewok.github.io/blob/master/src/FAlgebra.ipynb) for the complete worked out example.

## Proofs

Please see [the Appendix](https://github.com/anonymous-ewok/anonymous-ewok.github.io/blob/master/mechanization/Appendix.pdf) and the [mechanization](https://github.com/anonymous-ewok/anonymous-ewok.github.io/tree/master/mechanization) directory.

## Experiments

This project is organized as a vagrant box, and is built by running `make box-create` which pulls in all the required components, and builds the
required virutal machine. Next, running `make box-connect1` will let you connect you to the vagrant box, and once inside the box, you can
run `starttests.sh` from the home directory to start the experiments.
