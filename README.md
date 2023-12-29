# hyperoracle-assignment
This repository contains code to the halo2 implementation of following 2 algorithms:  
- bubblesort
- aes128 encryption

## High-level design 
### Bubblesort
**Goal**: Implement the bubblesort sorting algorithm in halo2 proving each step of the algorithm.   
**Notes**:
* The Plonkish table has 1 selector column, `ARR_SIZE` number of advice columns for storing array elements, 2 advice columns for the swapped elements per (swap) step, 1 range check table used by the `is_less_than` gadget, 1 instance column to expose the input and output array. 
* Layout of the Plonkish table is as follows:
```Batchfile
 __________________________________________________________________________________________________________
| q_swap_index | arr_0 | arr_1 | ... | arr_(ARR_SIZE-1) | range_check table | value_l | value_r | instance |
|-------------------------------------------------------------------------------------|--------------------|
|              |       |       |     |                  |                   |         |         |          | 
|              |       |       |     |                  |                   |         |         |          |
.              .       .       .     .                  .                   .         .         .          .
.              .       .       .     .                  .                   .         .         .          .
.              .       .       .     .                  .                   .         .         .          .
|______________|_______|_______|_____|__________________|___________________|_________|_________|__________|
```
* Each row of the advice columns stores the resulting array after each swap step of bubblesort, the swapped elements are copied to the value_l, value_r advice columns, which the `is_less_than` gadget uses to perform the check.

### AES 128
`Goal`: Implement the 10 rounds AES 128 encryption algorithm in halo2.   
`Notes`:   
* a 
