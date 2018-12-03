REGISTRY='registry.jorgeadolfo.com'
IMAGE='epav'
VERSION='latest'
NAME=$(IMAGE)
FULLNAME=$(REGISTRY)/$(IMAGE):$(VERSION)

make:
	docker build -f docker/Dockerfile -t $(FULLNAME) .

run:
	./bin/run.sh example/tosca-conf.yml example/user.smt

run-no-rules:
	./bin/run.sh example/tosca-conf.yml

clean:
	rm -fr experiments
	mkdir experiments
	touch experiments/.gitkeep

.PHONY: run run-no-rules clean
