# YoYoTricks
Code that implement attacks presented in "Yoyo Tricks with AES", ASIACRYPT 2017

3RoundDistinguisher.c:
Implements trivial distinguisher for 3 rounds AES using 3 texts

4RoundDistinguisher.c:
Implements trivial distinguisher for 4 rounds AES using 4 texts

5RoundDistinguisher.c:
Implements secret-key distinguisher for 5 rounds of AES using approx. 2^25 texts. 


5RoundKeyrecovery.c:
Implements key-recovery for 5 rounds using <= 2^11 texts and < 2^31 computational complexity. When the first 32-bit subkey is found, the rest of the three subkeys are found ultra-fast. 

