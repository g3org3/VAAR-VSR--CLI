make:
	docker build -f docker/Dockerfile -t registry.jorgeadolfo.com/epav:1.0.1 .
run:
	./bin/run.sh example/tosca-conf.yml example/user.smt
run-no-rules:
	./bin/run.sh example/tosca-conf.yml

clean:
	rm -fr experiments
	mkdir experiments
	touch experiments/.gitkeep

.PHONY: run run-no-rules clean
