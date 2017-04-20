FROM ubuntu:15.10
RUN apt-get update
RUN apt-get install -y apt-utils
RUN apt-get install -y python3-pip
RUN apt-get install -y libzmq3-dev
RUN pip3 install jupyter
ENV PATH /root/.local/bin:$PATH

RUN mkdir /notebooks
ENTRYPOINT jupyter notebook --NotebookApp.port=8888 '--NotebookApp.ip=*' --NotebookApp.notebook_dir=/notebooks
EXPOSE 8888
