# INSTALLATION

We assume that you have downloaded the
[ewok.box](https://zenodo.org/record/4455546)
as described in the README.md

This file is a very basic set of installation instructions. For detailed
information, refer to README.md

First, verify the downloaded box.

```bash
$ du -ksh ewok.box
7.1G ewok.box
```

The _md5_ checksum.

```bash
$ md5sum ewok.box
2aecab1ae5472a4cb5197ee40e0bc761  ewok.box
```

The installation requires [VirtualBox](https://www.virtualbox.org/) and [Vagrant](https://www.vagrantup.com/)
installed. Further, all tests were conducted on a 16GB RAM base box, and the
host needs at least 10GB RAM (16GB is recommended). Further, the port `8888`
in the host should be free as it is forwarded from the guest VM.

The downloaded box can be imported as follows:

```bash
$ vagrant box add ewok ./ewok.box
$ vagrant init ewok
$ vagrant up
```

You can verify the box import by the following command, which gets you a shell
in the VM

```bash
vagrant ssh
```

Once in the VM, verify the box as follows 

```bash
vm$ pwd
/home/vagrant
vm$ free -g
              total        used        free      shared  buff/cache   available
Mem:              9           0           9           0           0           9
Swap:             1           0           1
```

It contains the following files

```bash
vm$ ls
ewok  startjupyter.sh  starttests.sh  table1.sh  table2.sh
```

You can verify the completeness of the installation by invoking Jupyter viewer

```bash
vm$ ./startjupyter.sh
...
     or http://127.0.0.1:8888/?token=ba5e5c480fe4a03d56c358b4a10d7172d2b19ff4537be55e
```

Copy and paste the last line to your host browser to view the Jupyter notebook.
Note that token is a session id, and changes each time you start.

