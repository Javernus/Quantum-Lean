Many algorithms in Quantum Computing consider what is called an _oracle_. We denote this oracle with $O_{s}$. It is a special gate with behaviour corresponding to a known function $f$ with the secret input $s$ that it receives beforehand. A single application of the oracle should be interpreted as a single access to the secret input string $s$ through function $f$.

To consider what an oracle implies, I will compare the _classical_ oracle to the _quantum_ oracle. For a _classical_ oracle, the oracle maps any bitstring $t \mapsto f(t)$ for the oracle function $f$. This function $f$ has access to the secret input string $s$, and could be any function with input $t$, such as the inner product between $s$ and $t$ modulo $2$. Any call to the oracle counts as a single access to $s$.

For the _quantum_ oracle, the oracle maps any qubit state $\forall t : \ket{t} \mapsto (-1)^{f(t)} \ket{t}$. Again, the function $f$ has access to the secret input string $s$ and can be any function with input $t$.

A simple example of an oracle would be $O_{s} = X^{s}$, an oracle taking in a secret input $s \in \{0, 1\}$. Its gate is different for when $s$ is _true_ ($0$) or _false_ ($1$): $I$ and $X$ respectively.
