#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <string.h>
#include <stdbool.h>

#include "memory.h"
#include "fail.h"

// --------------------------------------------------------------
// Macros for the header block
#define HEADER_SIZE 1
#define USER_BLOCK_START(block) (block + HEADER_SIZE)
#define ACTUAL_BLOCK_START(block) (block - HEADER_SIZE)
// Macros for the block size
#define USER_TO_ACTUAL_SIZE(size) ((size == 0) ? 2 : (size + HEADER_SIZE))
#define ACTUAL_TO_USER_SIZE(size) (size - HEADER_SIZE)
// Macros for the bitmap positions
#define WORD_POS(addr) (addr / VALUE_BITS)        // word offset in the bitmap
#define BIT_POS(addr) ((addr) & (VALUE_BITS - 1)) // bit offset in the word
// Macros for authenticity checks
#define IS_BIT_FREE(word, bitpos) (((~word) >> (bitpos)) & 1) // if bit is 0
#define IS_BLOCK_FREE(block) (header_unpack_tag(block) == tag_None)
#define IS_VADDR(addr) (((addr) & 0x3) == 0)

// --------------------------------------------------------------
// Pointer initializations for memory partitions
static value_t* memory_start = NULL;
static value_t* bitmap_start = NULL;
static value_t* heap_start = NULL;
static value_t* memory_end = NULL;
static value_t* freelist = NULL;

// ==============================================================
// Simple helper functions
// ==============================================================

// Header management

static value_t header_pack(tag_t tag, value_t size) {
  assert(size <= 0xFFFFFF);     // takes user size
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t* header_block) {
  return (tag_t)(header_block[0] & 0xFF);
}

static value_t header_unpack_size(value_t* header_block) {
  // returns user size, not the actual size
  return (header_block[0] & 0xFFFFFF00) >> 8;
}

// --------------------------------------------------------------
// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  if (p_addr != NULL) {     // To check the freelist end
    assert(memory_start <= p_addr && p_addr <= memory_end);
  }
  return (value_t)((char*)p_addr - (char*)memory_start);
}

static inline bool in_heap(value_t vaddr) {
  value_t* p_addr = addr_v_to_p(vaddr);
  return heap_start <= p_addr && p_addr < memory_end;
}

// ==============================================================
// Default memory interface
// ==============================================================

char* memory_get_identity() {
  return "with GC : mark and sweep";
}

void memory_setup(size_t total_byte_size) {
  memory_start = calloc(total_byte_size, 1);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = memory_start + (total_byte_size / sizeof(value_t));
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);
  memory_start = memory_end = NULL;
  bitmap_start = heap_start = NULL;
  freelist = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(ACTUAL_BLOCK_START(block));
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(ACTUAL_BLOCK_START(block));
}

// ==============================================================
// Free list manipulation functions
// ==============================================================

static inline void set_next(value_t* elem, value_t* tail) {
    elem[1] = addr_p_to_v(tail);
}

static inline value_t* get_next(value_t* elem) {
    return addr_v_to_p(elem[1]);
}

static inline bool check_end(value_t* elem) {
    return (elem[1] == addr_p_to_v(NULL));
}

// ==============================================================
// Set up memory partitions
// ==============================================================

static inline void make_bitmap(void* code_end) {
  assert(code_end != NULL);
  assert(bitmap_start == NULL);
  assert(heap_start == NULL);

  bitmap_start = code_end;

  size_t available_size = memory_end - bitmap_start;
  size_t bitmap_size = (available_size + VALUE_BITS - 1) / VALUE_BITS;

  heap_start = bitmap_start + bitmap_size;

  // Set all the bits to 0 by default (unallocated and marked)
  memset(bitmap_start, 0, bitmap_size * sizeof(value_t));
}

// --------------------------------------------------------------
void memory_set_heap_start(void* code_end) {
  assert(code_end != NULL);

  make_bitmap(code_end);

  assert(bitmap_start < heap_start);

  size_t heap_size = memory_end - heap_start;
  assert(heap_size >= 2);

  // Initialize the freelist
  freelist = heap_start;
  freelist[0] = header_pack(tag_None, ACTUAL_TO_USER_SIZE(heap_size));
  set_next(freelist, NULL);  
}

// ==============================================================
// Find best fit block in the heap
// ==============================================================

static value_t* find_block(value_t size) { // needs actual size
  assert(heap_start != NULL);
  assert(freelist != NULL);

  value_t* curr = freelist;
  value_t* prev = NULL;

  value_t* best = NULL;
  value_t* pre_best = NULL;

  value_t best_size = 0;
  
  // Main loop to find the best fit block
  while(true) {
    value_t free_size = USER_TO_ACTUAL_SIZE(header_unpack_size(curr));

    if (free_size == size) {
      // First priority: exact fit free block
      pre_best = prev;
      best = curr;
      break;
    } else if (free_size > size + 2) {
      // Next priority: free block bigger by at least 2 words
      if (best == NULL || free_size < best_size) {
        // For the first fit or a smaller block
        best_size = free_size;
        pre_best = prev;
        best = curr;
      }
    }

    prev = curr;

    if (check_end(curr)) {
      // At the end of the freelist
      break;
    } else {
      // Get next free block
      curr = get_next(curr);
    }
  }

  if (best == NULL) {
    // If no free block found
    return NULL;
  }

  // ------------------------------------------------------------
  // Update the free list according to the best fit found

  value_t found_size = USER_TO_ACTUAL_SIZE(header_unpack_size(best));
  value_t remaining_size = found_size - size;

  // For the simple case of a single free block
  if (pre_best == NULL && check_end(best)) {
    assert(best == freelist);

    if (remaining_size < 2) {
      // In case an exact block doesn't leave enough space
      return NULL;
    } else {
      // Break into a smaller free block
      freelist += size;
      freelist[0] = header_pack(tag_None, ACTUAL_TO_USER_SIZE(remaining_size));
      set_next(freelist, NULL);

      return best;
    }
  }

  // For multiple free blocks (potentially) available after M&S
  if (remaining_size == 0) {
    // Remove entire free block if exact fit

    if (pre_best == NULL) {
      // For the first entry
      assert(best == freelist);
      freelist = get_next(best);

    } else if (!check_end(best)) {
      // For some middle entry
      assert(best != freelist);
      assert(get_next(pre_best) == best);
      set_next(pre_best, get_next(best));

    } else {
      // For the last entry
      assert(best != freelist);
      assert(get_next(pre_best) == best);
      set_next(pre_best, NULL);
    }
  } else {
    // Break into a smaller block if not exact fit
    value_t* best_end = best + size;
    best_end[0] = header_pack(tag_None, ACTUAL_TO_USER_SIZE(remaining_size));

    if (pre_best == NULL) {
      // For the first entry
      assert(best == freelist);
      freelist = best_end;
      set_next(best_end, get_next(best));

    } else if (!check_end(best)) {
      // For some middle entry
      assert(best != freelist);
      assert(get_next(pre_best) == best);
      set_next(pre_best, best_end);
      set_next(best_end, get_next(best));

    } else {
      // For the last entry
      assert(best != freelist);
      assert(get_next(pre_best) == best);
      set_next(pre_best, best_end);
      set_next(best_end, NULL);
    }    
  }

  return best;
}

// ==============================================================
// Bitmap manipulation functions
// ==============================================================

static inline size_t bitmap_pos(value_t vaddr) {
  assert(bitmap_start != NULL);
  assert(in_heap(vaddr));

  value_t heap_vaddr = addr_p_to_v(heap_start);
  size_t pos = (size_t) ((vaddr - heap_vaddr) / sizeof(value_t));

  return pos;
}

static inline bool is_bit_marked(value_t vaddr) {
  assert(bitmap_start != NULL);
  assert(in_heap(vaddr));

  size_t pos = bitmap_pos(vaddr);
  size_t word_pos = WORD_POS(pos);
  value_t byte_value = bitmap_start[word_pos];

  return !IS_BIT_FREE(byte_value, BIT_POS(pos));
}

static inline void mark_bit(value_t vaddr) {
  assert(in_heap(vaddr));
  assert(!is_bit_marked(vaddr));

  size_t pos = bitmap_pos(vaddr);
  bitmap_start[WORD_POS(pos)] = bitmap_start[WORD_POS(pos)] | (UINT32_C(1) << BIT_POS(pos));

  assert(is_bit_marked(vaddr));
}

static inline void unmark_bit(value_t vaddr) {
  assert(in_heap(vaddr));
  assert(is_bit_marked(vaddr));

  size_t pos = bitmap_pos(vaddr);
  bitmap_start[WORD_POS(pos)] = bitmap_start[WORD_POS(pos)] & ~(UINT32_C(1) << BIT_POS(pos));
  
  assert(!is_bit_marked(vaddr));
}

// ==============================================================
// Memory allocation function(s)
// ==============================================================

// Function prototypes for the garbage collector
void recursive_mark(value_t* root);
void sweep(void);
void garbage_collector(roots_t* roots);

// --------------------------------------------------------------

// Main function used for memory allocation
value_t* memory_allocate(tag_t tag, value_t size, roots_t* roots) {
  const value_t actual_size = USER_TO_ACTUAL_SIZE(size);

  // Find a free block in the heap
  value_t* fblock = find_block(actual_size);

  if (fblock == NULL) {
    // Run the mark-and-sweep GC if no block was found
    garbage_collector(roots);

    if (freelist!= NULL) {
      // Try to find a free block again
      fblock = find_block(actual_size);
    }

    if (fblock == NULL) {
      // If still no block found, trigger error message
      fail("no memory left (block of size %u requested)\n", size);
    }
  }

  // Update header if free block found
  assert(tag != tag_None);
  fblock[0] = header_pack(tag, size);

  // Mark the cooresponding entry in the bitmap
  value_t* user_block = USER_BLOCK_START(fblock);
  mark_bit(addr_p_to_v(user_block));

  return user_block;
}

// Call memory_allocate for both registers Lb and Ob
void memory_allocate_lb_ob(value_t l_size, value_t o_size, roots_t* roots) {
  roots->Lb = memory_allocate(tag_RegisterFrame, l_size, roots);
  roots->Ob = memory_allocate(tag_RegisterFrame, o_size, roots);
}

// ==============================================================
// Mark-and-Sweep Garbage Collector
// ==============================================================

void garbage_collector(roots_t* roots) {
  // Recursively mark (set to 0) all reachable blocks
  recursive_mark(roots->Lb);
  recursive_mark(roots->Ib);
  recursive_mark(roots->Ob);

  // Sweep unmarked (which are 1) blocks into freelist
  sweep();
}

// --------------------------------------------------------------
void recursive_mark(value_t* root) {
  value_t vaddr = addr_p_to_v(root);

  // Check if bitmap bit is marked
  if (in_heap(vaddr) && is_bit_marked(vaddr)) {
    // Found a reachable block in the heap
    unmark_bit(vaddr);

    value_t block_size = memory_get_block_size(root);

    for (unsigned int i = 0; i < block_size; i++) {
      assert(root + i < memory_end);

      value_t content = root[i];
      if (in_heap(content) && IS_VADDR(content)) {
        // If the block's content is a pointer address
        recursive_mark(addr_v_to_p(content));
      }
    }
  }
}

// --------------------------------------------------------------
void sweep() {
  value_t* curr = heap_start;
  value_t* prev_free = NULL;

  value_t block_size = 0;
  freelist = NULL;

  while(curr < memory_end) {
    value_t vcurr = addr_p_to_v(USER_BLOCK_START(curr));
    
    if (is_bit_marked(vcurr) || IS_BLOCK_FREE(curr)) {
      // Found an unreachable or free block
      if (is_bit_marked(vcurr)) {
        unmark_bit(vcurr);  
      }

      assert(!is_bit_marked(vcurr));

      if (prev_free == NULL) {
        // Found first block after a reachable block
        prev_free = curr;
        block_size = header_unpack_size(curr);
      } else {
        // Coalesce block with the previously found block
        value_t old_size = USER_TO_ACTUAL_SIZE(header_unpack_size(prev_free));
        block_size = old_size + USER_TO_ACTUAL_SIZE(header_unpack_size(curr));
      }
    } else {
      // Found a reachable block
      mark_bit(vcurr);

      if (prev_free != NULL) {
        // If any unreachable or free block was found
        assert(block_size != 0);
        prev_free[0] = header_pack(tag_None, block_size);
        set_next(prev_free, freelist);
        freelist = prev_free;
        prev_free = NULL;
      }
    }

    // Get next block from the heap
    curr += USER_TO_ACTUAL_SIZE(header_unpack_size(curr));
  }

  // Fall-through case
  if (prev_free != NULL) {
    assert(block_size != 0);
    // If the end of the heap is not a reachable block
    prev_free[0] = header_pack(tag_None, block_size);
    set_next(prev_free, freelist);
    freelist = prev_free;
  }
}

// --------------------------------------------------------------
// End of code
