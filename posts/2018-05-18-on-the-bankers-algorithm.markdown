---
title: On the banker's algorithm
---

In this post, we'll learn the banker's algorithm and why it can be used to determine whether a multiprogram will deadlock. I'll be pretty fast and loose with my use of "processes" vs. "threads" because the abstractions are the same.

## Motivation

Operating systems generally support the ability to run multiple processes simultaneously. Inevitably, processes share memory to communicate information, so the concurrent modification of this data can be a source of error. In practice, simultaneous accesses to the same part of memory by multiple processes is executed as a non-deterministic/time-dependent sequence of accesses, so we can observe different _interleavings_ of accesses over different executions of the same program.

Without pretense however, a sequential read and write or sequential writes by two separate processes to the same part of memory, or _data races_, are problematic because each interleaving of these actions will produce a different state of memory. We expect the same program behavior under all interleavings, so we need a mechanism to avoid data races, and more generally, any unwanted interleavings. _Mutual exclusion_ structures (locks, semaphores, etc.) can be used to avoid data races and unwanted interleavings by allowing processes to (wait to) acquire and relinquish exclusive access to parts of memory for any period of time.

However, mutual exclusion is dangerous. For the rest of this post, we'll conflate the mutual exclusion structure guarding a part of memory with the part of memory itself and call it a _resource_, because in practice, they're indistinguishable. Now, consider the following scenario: there are two concurrently executing processes $P_1$ and $P_2$ that would like to acquire (exclusive) access to resources $R_1$ and $R_2$ in memory. $P_1$ attempts to and successfully acquires $R_1$ while $P_2$ attempts the same, and $P_2$ attempts to and successfully acquires $R_2$ at the same time $P_1$ attempts to do the same. This circular dependence is called _deadlock_.

Since neither process relinqushes access to either resource, $P_1$ and $P_2$ wait indefinitely (_starvation_) to acquire $R_2$ and $R_1$, respectively. In other words, **deadlock implies starvation**, or equivalently, **no starvation implies no deadlock**

Note that **starvation does not necessarily imply deadlock**---processes can starve without a circular dependence. For example, let $P_1$ acquire $R$ and then let $P_2$ attempt to acquire $R$. If $P_1$ never releases $R$, then $P_2$ will starve, but $P_1$ is not attempting to acquire a resource held by $P_2$.

We can design programs to statically guarantee the absence of deadlock (_deadlock prevention_), or we can have our operating system allocate memory to processes dynamically in a way that avoids deadlock over their lifetime (_deadlock avoidance_). The banker's algorithm determines whether this is possible.

## Banker's Algorithm

In practice, the system must delay certain acquisitions and find a schedule that avoids deadlock. The acquisition method for each process would look something like this:

```
Process::Acquire(resource_type) {
  atomically {
    wait until system can grant 1 resource of type resource_type;
    immediately acquire 1 resource of said type;
  }
}
```

To determine whether the system can actually grant a certain acquisition at a certain time, we can simulate the acquisition and check whether the system could potentially deadlock. That is, **the system will _not_ deadlock if it can allocate its remaining resources to each process in some order such that each process gets all the resources it needs to execute.**

Here are some simplifying assumptions we'll make about our operating system and processes. The OS knows how many resources it can allocate to a fixed number of processes. Over time, each process attempts to acquire and release resources up-to a self-declared maximum. Therefore, "all the resources \[a process\] needs" are its maximum.

The banker's algorithm determines whether the system will not deadlock in the way we described above. We'll study it through example; let there be $n=4$ processes and $m=3$ types of resources. Here's what we need to know.

1. $\textsf{Total}:=\begin{bmatrix}9\\12\\12\end{bmatrix}\in\mathbb{N}^m$ where $\textsf{Total}_i$ is the total number of resources of type $i$ in this system

2. $\textsf{Max}:=\begin{bmatrix} 
3 & 4 & 4\\ 
3 & 5 & 3\\ 
4 & 6 & 3\\ 
1 & 4 & 2
\end{bmatrix}\in\mathbb{N}^{n\times m}$ where process $i$ may acquire at most $\textsf{Max}_{i,j}$ resources of type $j$ over its lifetime i.e. independent of time.

3. $\textsf{Alloc}:=\begin{bmatrix} 
1 & 2 & 3\\ 
2 & 1 & 3\\ 
4 & 5 & 3\\ 
1 & 2 & 2
\end{bmatrix}\in\mathbb{N}^{n\times m}$ where process $i$ currently holds $\textsf{Alloc}_{i,j}$ resources of type $j$

Consquently, $\textsf{MaxReq}=\textsf{Max}-\textsf{Alloc}$ is the resources of each type remaining to be allocated to each process.

Now, there are $\textsf{Avail}_j:=\textsf{Total}_j-\sum_{i=1}^n\textsf{Alloc}_{i,j}=\begin{bmatrix}1\\2\\1\end{bmatrix}\in\mathbb{N}^m$ resources of type $j$ available for allocation.

We will attempt to find a safe sequence of allocations. We will iteratively build up a sequence until we have included all processes---at each step, if we find a process $i$ (in order) such that $\textsf{MaxReq}_{i,j}\leq\textsf{Avail}_j$ for all $j$ i.e. the system can accommodate the allocation with the resources it has, then we can append this to our sequence and continue, updating $\textsf{Avail}_j:=\textsf{Avail}_j+\textsf{Alloc}_{i,j}$ for all $j$, with the idea that the process has terminated and we can reclaim its resources.

By applying this process, the safe sequence is processes 2, 3, 0, and 1, with $\textsf{Avail}$ evolving like so over time:

$$\begin{bmatrix}5\\7\\4\\\end{bmatrix},\begin{bmatrix}6\\9\\6\\\end{bmatrix},\begin{bmatrix}7\\11\\9\\\end{bmatrix},\begin{bmatrix}9\\12\\12\\\end{bmatrix}$$

## Conclusion

Maybe you'll think twice about using threads.
