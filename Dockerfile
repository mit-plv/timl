FROM ubuntu:17.04
RUN apt-get update
RUN apt-get install -y apt-utils
RUN apt-get install -y python3-pip
RUN apt-get install -y libzmq3-dev
RUN pip3 install jupyter
ENV PATH /root/.local/bin:$PATH

RUN apt-get install -y z3=4.4.1\*
RUN apt-get install -y ruby
RUN apt-get install -y smlnj libsmlnj-smlnj ml-yacc ml-ulex
RUN apt-get install -y mlton

ENV TIML /timl

WORKDIR $TIML

ADD . $TIML
ENV PATH $PATH:$TIML
ENV PYTHONPATH $PYTHONPATH:$TIML/jupyter

RUN mkdir -p /root/.local/share/jupyter/kernels/timl
RUN ln -s $TIML/jupyter/timl-kernel.json /root/.local/share/jupyter/kernels/timl/kernel.json
RUN jupyter kernelspec install ~/.local/share/jupyter/kernels/timl

RUN mkdir /notebooks
RUN cp $TIML/jupyter/TiML-example-notebook.ipynb /notebooks
RUN cp -r $TIML/examples /notebooks
ENTRYPOINT jupyter notebook --allow-root --NotebookApp.port=8888 '--NotebookApp.ip=*' --NotebookApp.notebook_dir=/notebooks --NotebookApp.token=''
EXPOSE 8888
