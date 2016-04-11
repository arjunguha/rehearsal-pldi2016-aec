TRIALS=1
.PHONY = all clean

all: idempotence.pdf determinism.pdf sizes.pdf scalability.pdf
	@echo "Complete.\nSee idempotence.pdf, determinism.pdf, sizes.pdf, and scalability.pdf"

clean:
	rm -f sizes.csv idempotence.csv determinism.csv scalability.csv sizes.pdf idempotence.pdf determinism.pdf scalability.pdf

scalability.csv:
	(cd ..; scala scripts/Benchmarks.scala scalability $(TRIALS) results/scalability.csv)

scalability.pdf: scalability.csv
	(cd ../scripts; R --file=scalability.r)

sizes.csv:
	(cd ..; scala scripts/Benchmarks.scala sizes results/sizes.csv)

sizes.pdf: sizes.csv
	(cd ../scripts; R --file=sizes.r)

idempotence.csv:
	(cd ..; scala scripts/Benchmarks.scala idempotence $(TRIALS) results/idempotence.csv)

idempotence.pdf: idempotence.csv
	(cd ../scripts; R --file=idempotence.r)

determinism.csv:
	(cd ..; scala scripts/Benchmarks.scala determinism $(TRIALS) results/determinism.csv)

determinism.pdf: determinism.csv
	(cd ../scripts; R --file=determinism.r)
