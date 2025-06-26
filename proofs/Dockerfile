FROM rocq/rocq-prover:9.0-native
ADD --chown=1000:1000 . /proofs/
WORKDIR /proofs
RUN make
RUN make coqdoc
