# Replication package for _Input Algebras_

**IMPORTANT** This complete source code of this artifact is hosted
[in this Github repository](https://github.com/vrthra/Ewoks).

Our submission is both a tool that implements the algorithm given in the paper
_Input Algebras_, as well as the Jupyter notebook that explains the algorithm,
and the experiments with the tool. You can obtain the Vagrant VM image from
<https://doi.org/10.5281/zenodo.4455545.>.
which contains the complete artifacts necessary to reproduce our experiments.
We describe the process of invoking the virtual machine below.

We also note that if you are unable to download the vagrant box (It is 7 GB)
You can also take a look at the complete worked out algorithm and running
examples of how to derive the specialized grammar at
[src/FAlgebra.ipynb](https://github.com/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb).
It can be viewed either by using the virtual box as explained below, or can be directly
viewed using any of the Jupyter notebook viewers such as VSCode. A
non-interactive version hosted at Github is accessible [from this link](https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb)

## Rebuilding the vagrant box

If you are checking out the original repository from https://github.com/vrthra/ewoks
and want to rebuild this vagrant box, then, after checking out, simply execute
`make box-create` in the root directory. **This is not necessary if you are
directly downloading the vagrant box** from <https://doi.org/10.5281/zenodo.4455545.>

```bash
$ make box-create
```

## Overview

This paper presents a novel general algorithm for specializing the
base context-free grammar towards certain behaviors such as specific
failures.  Our tool _evogram_ takes a program, its grammar and a
failure/behavior inducing input, and automatically infers an evocative
pattern that characterizes the failure/behavior.
This pattern represents a specialized context-free grammar that guarantees
to have the failure inducing fragment. Such patterns can then be combined
algebraically using the full boolean operations such as conjunction
disjunction and negation.

We evaluate `evogram` on a variety of subjects.


## Prerequisites

### RAM

All experiments done on a VM with **16 GB RAM**.

### Setup

First, please make sure that the port 8888 is not in use. Our VM forwards its
local port 8888 to the host machine.

#### Download

Next, please download the vagrant box from the following link:

<https://doi.org/10.5281/zenodo.4455545.>.

This produces a file called `ewok.box` which is 7.1 GB in size
(the commands in the host system are indicated by
leading `$` and the other lines indicate the expected output),

```bash
$ du -ksh ewok.box
7.1G  ewok.box
```

and should have the following _md5_ checksum.

```bash
$ md5sum ewok.box
1185033617d029143cf9ab331ab48cf4 ewok.box
```

#### Importing the box

The vagrant box can be imported as follows:

```bash
$ vagrant box add ewok ./ewok.box
==> box: Box file was not detected as metadata. Adding it directly...
==> box: Adding box 'ewok' (v0) for provider:
    box: Unpacking necessary files from: file:///path/to/ewok/ewok.box
==> box: Successfully added box 'ewok' (v0) for 'virtualbox'!

$ vagrant init ewok
A `Vagrantfile` has been placed in this directory. You are now
ready to `vagrant up` your first virtual environment! Please read
the comments in the Vagrantfile as well as documentation on
`vagrantup.com` for more information on using Vagrant.

$ vagrant up

Bringing machine 'default' up with 'virtualbox' provider...
==> default: Importing base box 'ewok'...
==> default: Matching MAC address for NAT networking...
==> default: Setting the name of the VM: vtest_default_1591177746029_82328
==> default: Fixed port collision for 22 => 2222. Now on port 2200.
==> default: Clearing any previously set network interfaces...
==> default: Preparing network interfaces based on configuration...
    default: Adapter 1: nat
==> default: Forwarding ports...
    default: 8888 (guest) => 8888 (host) (adapter 1)
    default: 22 (guest) => 2200 (host) (adapter 1)
==> default: Running 'pre-boot' VM customizations...
==> default: Booting VM...
==> default: Waiting for machine to boot. This may take a few minutes...
    default: SSH address: 127.0.0.1:2200
    default: SSH username: vagrant
    default: SSH auth method: private key
==> default: Machine booted and ready!
==> default: Checking for guest additions in VM...
==> default: Mounting shared folders...
    default: /vagrant => /path/to/ewok
```

#### Verify Box Import

The commands inside the guest system are indicated by a `vm$ ` prefix.
Anytime `vm$` is used, it means to either ssh into the vagrant box as below, or
if you are already in the VM, use the shell inside VM.

```bash
$ vagrant ssh

vm$ free -g
              total        used        free      shared  buff/cache   available
Mem:             15           0          15           0           0           9
Swap:             1           0           1
```

## A complete example

```bash
vm$ pwd
/home/vagrant
vm$ ls
ewok  startjupyter.sh  starttests.sh compile_notebook.sh table1.sh  table2.sh
```

The following are the important files

| File/Directory               | Description                                                                 |
|------------------------------|-----------------------------------------------------------------------------|
| startjupyter.sh              | The script to start Jupyter notebook to view examples. |
| starttests.sh                | Start the experiments. |
| tables1.sh                   | CLI for viewing the results from fuzzing experiments. |
| tables2.sh                   | CLI for viewing the results from recognizing experiments. |
| ewok/src/                    | The main _ewogram_ algorithm implementation. |
| ewok/src/FAlgebra.ipynb      | The detailed _ewogram_ notebook which contains explanations in _Python_. |
| compile_notebook.sh          | Execute and convert the _ewogram_ notebook to HTML for offline viewing (non-interactive) |

The most important file here is `ewok/src/FAlgebra.ipynb` which is the
Jupyter notebook that contains the complete algorithm explained and worked out
over multiple examples. It can be interactively explored using any of the
Jupyter notebook viewers including VSCode or directly using a browser as explained below.

It can also be viewed (read only) directly using the Github link
[here](https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb).

### Viewing the Jupyter notebook

**IMPORTANT**: By default, the notebook is set to password less login
If you prefer to enable password, before starting the Jupyter notebook, modify
`ewok/jupyter_notebook_config.py` and change the following lines as given below.

```
## Hashed password to use for web authentication.
#  
#  To generate, type in a python/IPython shell:
#  
#    from notebook.auth import passwd; passwd()
#  
#  The string should be of the form type:salt:hashed-password.
# ewok
c.NotebookApp.password = 'sha1:cfd85c86a739:b14a96df5fc8881742ec09fb2d2842d288880cd1'
…
c.NotebookApp.password_required = True
```

To start the Jupyter notebook, From within your VM shell, do the following:

```bash
vm$ ./startjupyter.sh
...
     or http://127.0.0.1:8888/?token=ba5e5c480fe4a03d56c358b4a10d7172d2b19ff4537be55e
```

Copy and paste the last line in the host browser. The port `8888` is forwarded
to the host.

Click the [src](http://127.0.0.1:8888/tree/src) link from the browser and within
that folder, click the [FAlgebra.ipynb](http://127.0.0.1:8888/notebooks/src/FAlgebra.ipynb)
link. This will let you see the complete set of examples as well as the
experiments in an already executed form.

**We recommend using the Jupyter notebook from the VM to explore the explanation
as the sidebar is very handy for navigation. Using the nbviewer directly does not
provide one with the sidebar**

## Starting the experiments

There are two sets of experiments: The fuzzing experiments and the recognizing
experiments. You can kick of both from the same command.

```bash
vm$ ./starttests.sh
```

## Result analysis

### Table 1

If all experiments have finished, the Table 1 can be created with the
following command:

```bash
vm$ ./table1.sh 
Bug                  |         xx% of          F |         xx% of      not F
find_07b941b1        |     100.00% of        100 |       5.00% of        100
find_93623752        |     100.00% of        100 |       5.00% of        100
find_c8491c11        |     100.00% of        100 |       2.00% of        100
find_dbcb10e9        |     100.00% of        100 |      13.00% of        100
grep_3c3bdace        |     100.00% of        100 |       0.00% of         94
grep_54d55bba        |     100.00% of        100 |       0.00% of         93
grep_9c45c193        |     100.00% of          1 |       1.08% of         93
```
The first column specifies how many of the generated inputs induced the
failure when using the grammar that guarantees at least one failure inducing
fragment (Note that containing the fragment itself may not be sufficient
guarantee if other semantics is involved).

The second column specifies how many of the generated inputs induced the
specified failure when using the grammar that negates the first. That is, a
guarantee that the particular fragment will not be present. As before, a
particular fragmentary pattern may not be the only fragment that induces
that given failure. For example, we can specify a pattern `<expr> / 0` to
indicate division by zero behavior, but the same behavior can also occur
when one gets `<expr> / ( 1 - 1)`.

### Table 2

Similarly, the Table 2 can be created using the following command

```bash
vm$ ./table2.sh 

clojure_2092         |      76.82% of        285 |      99.01% of        100
clojure_2345         |      75.14% of        266 |      98.21% of         55
clojure_2450         |      96.42% of        647 |      99.63% of        267
clojure_2473         |      96.29% of        701 |      98.31% of         58
clojure_2518         |      40.00% of          4 |      98.80% of         82
clojure_2521         |      76.14% of        469 |      99.11% of        111
closure_2808         |     100.00% of         64 |      92.59% of         25
closure_2842         |       1.51% of          4 |      98.86% of        173
closure_2937         |      96.82% of       1125 |      94.12% of         32
closure_3178         |      94.05% of        617 |      99.01% of        100
closure_3379         |      97.69% of        508 |      77.78% of         21
find_07b941b1        |      92.68% of        190 |     100.00% of          7
find_93623752        |      99.48% of        190 |     100.00% of          7
find_c8491c11        |      98.44% of        189 |     100.00% of          8
find_dbcb10e9        |     100.00% of        379 |     100.00% of          6
grep_3c3bdace        |      93.91% of        185 |     100.00% of         28
grep_54d55bba        |      87.31% of        172 |     100.00% of         24
grep_9c45c193        |      50.00% of          1 |     100.00% of         11
lua_5_3_5__4         |       4.71% of          9 |      98.61% of        142
rhino_385            |      93.20% of        452 |      94.74% of         18
rhino_386            |      98.40% of        369 |      93.18% of         41
…
```
The first column contains what percentage of inputs during reduction that
induced the given failure was recognized as containing the failure inducing
fragment using the specialized evocative grammar generated. The second column
contains what percentage of inputs during reduction that caused the failure
that was rejected using the negated evocative grammar.

**NOTE** You do not have to wait until the end of experiments to see the
results as they are produced. You can take a new shell using `vagrant ssh`
and execute both `table.sh` and `table2.sh` and you can see the current
results.

## How is the Jupyter notebook organized

The Jupyter notebook provided has complete documentation of the entire
algorithm. Each method is thoroughly documented, and executions of methods
can be performed to verify their behavior.
Use the Jupyter notebook as the main guide and for the interactive exploration
of the algorithm.

The notebook is split into two parts:

1. The explanation of the algebra
<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Algebra-of-Failure-Inducing-Input-Patterns>
2. The experiment
i<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Experiments>


### Algebra

1.1 What

Explanation of what we are trying to do with ewoks

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#What>

1.2 Why

Explanation of why we want to do it

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Why>

1.3 How

A very high level outline 

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#How>

1.4 How is it done

A slightly more detailed outline

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#How-is-it-done?>

1.5 Limitations

The limitations of our approach

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Limitations>

1.6 Magick

Jupyter notebook specific hooks so that it is comfortable to use. Ignore these.

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Magick>

1.7 Fault Patterns

A complete explanation of the _evocative patterns_ including the algorithms that
show how it is extracted. This section also contains a few generic common
library functions for later use.

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Fault-Patterns>

1.8 Inserting a Fault

Given a fault, and the failure causing fragment, how do we extract the fragment
as the _evocative patter_, and then insert this evocative pattern into the base
grammar thus specializing it.

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Inserting-a-fault>

1.9 Reconstruct

During the fault insertion,  we introduce a number of new keys into the grammar.
This step produces the definitions for these keys from the existing keys in the
grammar. This step is needed for every operation.

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Reconstruct>

2.0 Conjunction

Producing a conjunction `(e1 & e2)` of two _evocative expressions_.

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Conjunction>

2.1 Disjunction

Producing a disjunction `(e1 | e2)` of two _evocative expressions_.

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Disjunction>

2.2 Negation

Producing the negation not(e) of an _evocative expression_. Negation is used
with conjunction to produce difference. That is, `e1 - e2 == e1 & (-e2)`

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Negation-(self)>

2.3 Difference

Use the negation to produce difference (for example, see experiments).
Please ignore partial orders.

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Difference>

### Experiment

2.1 Fault A

The evocative pattern is: `((<expr>))`

We also provide a negation (not A).

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Fault-A-(exactly-1)>

2.2 Fault B

The evocative pattern is: `<term> + <term>`

We also provide a negation (not B).

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Fault-B>

2.3 Fault C

The evocative pattern is: `<factor> / 0`

We also provide a negation (not C).

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#Fault-C>

2.4 Conjunction

Given: `A & B`, `A & C`, `B & C`

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#A-&-B>

2.5 Disjunction

Given: `A | B`, `A | C`, `B | C`

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#A-|-B>

2.6 Negation

Given: `A - B`, `A - C`, `B - C`

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#A---B>

2.7 More Complex

Given: `A & B & C`, `A | B | C`, ` A & B | C`

<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#More>

2.8 JSON

Describes the two examples in the paper -- null key-value `<string>:null`, its negation, 
empty key `"":<element>`, and their conjunction.


<https://nbviewer.jupyter.org/github/vrthra/Ewoks/blob/master/src/FAlgebra.ipynb#JSON>


## How to add a new subject

To add a new subject (with some bugs to abstract), one needs the following

* The grammar that can parse the subject in the canonical form defined by the
  [Parser in fuzzingbook](https://fuzzingbook.org/html/Parser.html). If you
  have an ANTLR grammar, it can be converted to the fuzzingbook format using 
  [this project](https://github.com/vrthra/antlr2json).

* The bugs you have collected

* The interpreter/compiler/command that accepts some input file. 

Do the following:

* make a directory for your interpreter under `lang`, say `mycmd`
* Under `lang/mycmd`, create three directories:
  * `lang/mycmd/bugs`
  * `lang/mycmd/compilers`
  * `lang/mycmd/grammar`
* Under `grammar`, place the JSON grammar that you have, and call it
  say `lang/mycmd/grammar/mycmd.fbjson`
* Under bugs, one file per bug, place each bugs. Say `lang/mycmd/bugs/cmd_1.cmd`
* Under `compilers` place your compiler/command executable. Say `lang/mycmd/compilers/cmd`
* Under `src` directory, one file per bug, add test cases with the following format

```python
import Infra as I
from Abstract import PRes

def my_predicate(src):
    # this following line defines how the interpreter is invoked. The first
    # string is the label, and second string is the command used to execute.
    # src will have the source
    o = I.do('mycmd', './lang/mycmd/compilers/cmd', src)

    # Now, define the behavior you want. PRes.success means the failure was
    # reproduced, while PRes.invalid means the input was semantically invalid
    # and we will ignore this input. PRes.failure is a semantically valid input
    # that could not reproduce the failure.

    if o.returncode == 0: return PRes.failed
    if o.returncode == -11: return PRes.success
    out = o.stdout
    if 'Segmentation fault (core dumped)' in out:
        return PRes.success
    elif 'stack traceback' in out:
        return PRes.invalid
    elif 'TIMEOUT' in out:
        return PRes.timeout
    return PRes.failed

import sys
if __name__ == '__main__':
    # Here we define the paths
    I.main('./lang/mycmd/grammar/mycmd.fbjson', './lang/mycmd/bugs/cmd_1.cmd', my_predicate)
```
Once this predicate is written to file say as `src/mycmd_1.py`, invoking it,
using `python3 src/mycmd_1.py` will produce the correctly abstracted file under
`result/cmd_1.cmd.json`. The specialized grammar that guarantees at least
one fault fragment is written in the following file, which can be viewed as follows:

```
vm$ cat results/mycmd_1_atleast_one_fault_g.json | jq . -C | less -R
```

### Fuzzer

The same predicate can also be used to fuzz by producing a new file `src/fuzz_cmd_1.py` with
the following contents

```python

import Fuzz as F
import mycmd_1 as Main

import sys
if __name__ == '__main__':
    F.main('./lang/mycmd/grammar/mycmd.fbjson', './lang/mycmd/bugs/cmd_1.cmd', Main.my_predicate)
```

Invoking this file using `python3 src/fuzz_mycmd_1.py` will produce the
fuzz output under `fuzzing/fuzz_mycmd_1.json`, which can be inspected for
results. The main results are written directly to stdout, which can
be captured for viewing. The most interesting lines are

```
Fuzz Atleast Total: XXX
Fuzz Atleast Valid: YY
Fuzz Atleast Success: ZZ

Fuzz NoFault Total: xxx
Fuzz NoFault Valid: yy
Fuzz NoFault Success: zz
```

Where `XXX` indicates the total number of fuzz inputs generated, out of which
`YY` were semantically valid, and out of that `ZZ` reproduced the failure.
Similarly using the negated grammar is presented with NoFault. `xxx` is the
total, `yy` is the semantically valid, and `zz` are the number of times the
particular behavior was induced using the grammar that rejects the fragment.

### Recognizer
Using it as a recognizer is similar. Produce a new file `src/recognize_cmd_1.py` with
the following contents

```python
import Recognize as R
import mycmd_1 as Main

import sys
if __name__ == '__main__':
    R.main('./lang/lua/grammar/mycmd.fbjson', './lang/mycmd/bugs/cmd_1.lua', Main.my_predicate)
```

Now, we need inputs that can be used with the recognizer. We expect this
file named `results/cmd_1.log.json`. This file is generally produced during
reduction. But you can also provide your own. The format is like this

```json
{"res": "PRes.success", "key": "()", "src": "find . -regex '.*'"}
{"res": "PRes.failed", "key": "reduction:<find-expression>", "src": "find . "}
```
The `src` key contains the command invocation, and the `res` key contains the
result of executing this command. This file will be read by the next command
internally.

Invoking the recognizer using `python3 src/recognize_mycmd_1.py ` will produce
the fuzz output under `fuzzing/fuzz_mycmd_1.json`, which can be inspected for
results. The main results are written directly to stdout, which can
be captured for viewing. The most interesting lines are

```
 Recognize Success: XX/YY = ZZ%
 Recognize Fail xx/yy = zz%
```

The first line indicates that `XX` inputs out of `YY` inputs that induced
the failure were parsed successfully by our evocative grammar.
On the other hand, out of `yy` failure inducing inputs only `xx` was rejected
by the negated grammar.


**Grammar Format**

The grammar format we use is the [Fuzzingbook](https://www.fuzzingbook.org/html/Parser.html)
canonical JSON format, where the nonterminals are represented as keys of a
python `dict`, and each nonterminal is associated with a definition represented
by an `list` of `rules`, and each `rule` is again a `list` of tokens, and each
token can either be a nonterminal or a terminal symbol represented as a string.
Both original as well as specialized evocative grammars have the same format (and both are context-free).

You can view a grammar file using the following command

```
vm$ cat results/mycmd_1_atleast_one_fault_g.json | jq . -C | less -R
```

