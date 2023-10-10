#import "../../template.typ": template
#show: template

= Symmetric key ciphers

- *Symmetric key cipher*: one in which encryption and decryption keys are equal.
- *Key size*: $log_2 ("number of possible keys")$.
- *Caesar cipher*: shift all characters by a constant amount. Key size is $log_2 (26)$
- *Substitution cipher*: key is permutation of ${a, ..., z}$. Key size is $log_2 (26!)$.
- *Stirling's formula*: $ n! approx sqrt(2 pi n) (n / e)^n $
- If any statistical properties of plaintext are reflected in cipher text, then we can use this as basis for an attack. We compare the most common letters in the English language with the most common letters in the message. We can also compare letter pairs.
- *One-time pad*: key is random sequence of integers $mod 26$, $(k_1, k_2, ...)$. If message is $(m_1, m_2, ..., m_r)$ then ciphertext is $(c_1, c_2, ...) = (k_1 + m_1, k_2 + m_2, ...)$. To decrypt the ciphertext, $m_i = c_i - k_i$. Once $(k_1, ..., k_r)$ have been used, they must never be used again.
    - One-time pad is information-theoretically secure against ciphertext-only attack: $PP(M = m | C = c) = PP(M = m)$.
    - Keys must never be reused, so must be as long as message.
    - Keys must be truly random.