# -*- mode: ruby -*-
# vi: set ft=ruby :

Vagrant.configure("2") do |config|
  config.vm.box = "generic/ubuntu1804"
  config.vm.box_check_update = false
  # config.vm.network "private_network", ip: "192.168.10.50"
  config.vm.network "forwarded_port", guest: 8888, host: 18888, auto_correct: true#, disabled: true

  # we do not want a synced folder other than the default.
  # we will be extracting the tarred up ewok to home.
  config.vm.synced_folder "./ewok", "/vagrant/ewok"

  config.vm.provider "virtualbox" do |v|
    v.memory = 16096
    v.cpus = 2
  end

  config.vm.provision "shell", inline: <<-SHELL
    apt-get update
    apt-get -y install openjdk-11-jre-headless make docker.io graphviz python3-venv python3-pip remake jq kakoune
    pip3 install wheel
    pip3 install graphviz
    pip3 install jupyter
    pip3 install pudb
    pip3 install sympy
    pip3 install rich
    pip3 install psutil

    pip3 install jupyter_contrib_nbextensions
    pip3 install jupyter_nbextensions_configurator
    jupyter contrib nbextension install --sys-prefix
    jupyter nbextension enable toc2/main --sys-prefix

    echo cd /home/vagrant/ewok >  /home/vagrant/startjupyter.sh
    echo jupyter notebook --ip 0.0.0.0 --port 8888 >> /home/vagrant/startjupyter.sh
    chmod +x /home/vagrant/startjupyter.sh

    echo cd /home/vagrant/ewok >  /home/vagrant/table1.sh
    echo python3 src/table1.py >>  /home/vagrant/table1.sh
    chmod +x /home/vagrant/table1.sh

    echo cd /home/vagrant/ewok >  /home/vagrant/table2.sh
    echo python3 src/table2.py >>  /home/vagrant/table2.sh
    chmod +x /home/vagrant/table2.sh

    echo cd /home/vagrant/ewok >  /home/vagrant/starttests.sh
    echo make all >>  /home/vagrant/starttests.sh
    chmod +x /home/vagrant/starttests.sh

    echo cd /home/vagrant/ewok >  /home/vagrant/compile_notebook.sh
    echo jupyter nbconvert --to notebook --execute src/FAlgebra.ipynb --ExecutePreprocessor.timeout=36000 --output=FAlgebra_.ipynb >>  /home/vagrant/compile_notebook.sh
    echo jupyter nbconvert --to html src/FAlgebra_.ipynb --output=~/FAlgebra.html >>  /home/vagrant/compile_notebook.sh
    chmod +x /home/vagrant/compile_notebook.sh

  SHELL
end
