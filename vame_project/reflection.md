# Vame Dafny implementation Reflexion

Dafny is a language that tries its best to make sure that the code you are writing does exactly what you are expecting. This is good because it reduces significantly the amount of bugs and overall reliability on the code, but it can be very frustrating to work in it, because if Dafny does not understand you code to the fullest, it is not accepted.

Probably the most difficult part of this implementation was the lazy variant of the DecisionCache. Most of the alterations on the original DecisionCache were very simple and easy to implement, the hardest part was to prove that our implementation preserved validity. Dafny just would not accept our code, we had to add multiple assertions to our lookup method in order to prove that the modifications on the versions, values and keys arrays did not disprove it. What made this process hard was not creating new assertions, it was understanding what assertions we had to make to convince Dafny, since, for us, the proof that was already included sufficed.

In general, the example we just mentioned reflects our difficulties during the implementation of the specification. Nonetheless, this project was very enjoyable, succeeding in proving the correctness of your code is very rewarding.

Madalena Mota, ist1110355
Pedro Aldeia,  ist1109989