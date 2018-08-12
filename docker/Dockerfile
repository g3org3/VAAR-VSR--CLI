FROM python:2.7

RUN apt-get update && apt-get install -y unzip

WORKDIR /

# SETUP Z3
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-14.04.zip
RUN unzip *.zip
RUN rm *.zip
RUN mv z3-* z3
ENV Z3_LIBRARY_PATH "/z3/bin"

# SETUP tosca-parser
RUN git clone https://github.com/openstack/tosca-parser.git
WORKDIR /tosca-parser
RUN pip install -r requirements.txt
RUN python setup.py build
RUN python setup.py install

# SETUP THIS APP
RUN mkdir /cli
WORKDIR /cli
# DEPS
COPY lib/requirements.txt .
RUN pip install -r requirements.txt
# APP
COPY . .

COPY ./docker/entrypoint.sh /cli/entrypoint.sh
RUN chmod +x /cli/entrypoint.sh
ENTRYPOINT ["/cli/entrypoint.sh"]