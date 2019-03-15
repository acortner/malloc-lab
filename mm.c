/*
 * We used an explicit free  list
 *      8 byte aligned
 *      minimum size block of 16  bytes (4 – header, 8 – payload, 4 – footer).
 *      allocated blocks have format (Header --- Payload --- Footer)
 *      free blocks have format      (Header --- Prev block --- Next block --- Payload --- Footer)
 *      free list is a list of pointers to free blocks
 *      manipulates free list by finding first place where block fits
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team Name */
    "EECS 213 Struggles",
    /* First member's full name */
    "Andrew Cortner",
    /* First member's NetID */
    "ajc4628",
    /* Second member's full name (leave blank if none) */
    "Karen Bao",
    /* Second member's NetID */
    "kzb2826"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))



/* additional macros */
#define WSIZE 4 /* word size in bytes */
#define DSIZE 8 /* double word size in bytes */
#define CHUNKSIZE (1 << 13)

#define MAX(x, y) ((x) > (y)? (x) : (y)) /* gets max of two elements */

#define PACK(size, alloc) ((size) | (alloc)) /* pack a size and allocated bit into a word */

/* read and write a word at address p */
#define GET(p)         (*(unsigned int *)(p))
#define PUT(p, val)    (*(unsigned int *)(p) = (val))

/* read the size and allocated fields from address p */
#define GET_SIZE(p)   (GET(p) & ~0x7)
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((void *)(bp) - WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE((void *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE((void *)(bp) - DSIZE))

/* given block ptr bp, compute the address of the next/previous pointer */
#define NEXT_PTR(bp) (*(char **)(bp + WSIZE))
#define PREV_PTR(bp) (*(char **)(bp))

/* global variables */
static char *heap_listp = 0;
static char *free_list = 0;
char *epilogue = 0;
int free_blocks = 0; //counts amount of free blocks.

/* helper functions */
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *extend_heap(size_t num_words);
static void *find_fit(size_t asize);

/* free list functions */
static void add_to_freelist(void *bp);
static void remove_from_freelist(void *bp);

/* heap checker functions */
static int mm_check(void);
static int hc_valid(void);
static int hc_overlap(void);
static int hc_coalesce(void);
static int hc_freelist(void);

/*
 * mm_init - initialize the malloc package. 
 */
int mm_init(void)
{
  /*Create the initial empty heap, returns -1 if error, 0 if good  */
  if ((heap_listp = mem_sbrk(8 * WSIZE)) == NULL) {
      return -1;
  }

  PUT(heap_listp, 0); /* alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* prologue header */
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* prologue footer */
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); /* epilogue header */
  free_list = heap_listp + (2 * WSIZE);
  free_blocks = 0;
  epilogue = (heap_listp + (3 * WSIZE));

  /* extend empty heap with a free block of (min block size / word size) bytes */
  if (extend_heap(16/WSIZE) == NULL) {
      return -1;
  }
  return 0;
}
/* mm_malloc - always allocate a block whose size is a multiple of the alignment
 *      return a pointer to the block if allocation is successful, NULL otherwise
 */
void *mm_malloc(size_t size)
{
  size_t asize; /* adjusted block size */
  size_t extendsize; /* amount fo extend heap if no fit */
  void *ptr;

  /* ignore spurious requests */
  if (size == 0)
      return NULL;

  /* adjust block size to include overhead and alignment reqs */
  if (size > DSIZE)
      asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  else
      asize = (2 * DSIZE);

  /* search the free list for a fit */
  if ((ptr = find_fit(asize)) != NULL) {
      place(ptr, asize);
      return (ptr);
  }

  /* no fit found. get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((ptr = extend_heap(extendsize / WSIZE)) == NULL)
      return NULL;
  place(ptr, asize);
  return (ptr);
}

/*
 * mm_free - frees the block at the ptr
 */
void mm_free(void *ptr)
{
    /* ignore useless calls to free */
    if (ptr == NULL)
        return;
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - reallocates block at ptr to a block of at least size bytes
 *      if size = 0, free the block and return NULL
 *      if the block fits, do nothing
 *      if the requested size is too big and the next block is not allocated,
 *          combine both blocks and resize
 *      if we cannot do anything, malloc a new block and copy the two blocks over
 *          and return the address of this block
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (size < 0)
        return NULL;
    else if (size == 0) {
        mm_free(ptr);
        return NULL;
    } else {
        size_t old_size = GET_SIZE(HDRP(ptr));
        size_t new_size = size + (2 * WSIZE);
        if (new_size <= old_size)
            return ptr;
        else {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
            size_t csize = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
            if (!next_alloc && (csize >= new_size)) {
                remove_from_freelist(NEXT_BLKP(ptr));
                PUT(HDRP(ptr), PACK(csize, 1));
                PUT(FTRP(ptr), PACK(csize, 1));
                return ptr;
            } else {
                void *new_ptr = mm_malloc(new_size);
                place(new_ptr, new_size);
                memcpy (new_ptr, ptr, new_size);
                mm_free(ptr);
                return new_ptr;
            }
        }
    }
    return NULL;
}

/*
 * place - place a block of asize and split if the remainder of the block is at least 16
 */
static void place(void *ptr, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(ptr));
    
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        remove_from_freelist(ptr);
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(csize - asize, 0));
        PUT(FTRP(ptr), PACK(csize - asize, 0));
        coalesce(ptr);
    } else {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
        remove_from_freelist(ptr);
    }
}

/*
 * coalesce - coalesce if possible and return new block, otherwise return original pointer
 */
static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr))) || PREV_BLKP(ptr) == ptr;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    
    if (!prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr))) + GET_SIZE(HDRP(PREV_BLKP(ptr)));
        remove_from_freelist(PREV_BLKP(ptr));
        remove_from_freelist(NEXT_BLKP(ptr));
        ptr = PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        remove_from_freelist(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        ptr = PREV_BLKP(ptr);
        remove_from_freelist(ptr);
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    add_to_freelist(ptr);
    // mm_check();
    return ptr;
}

/*
 * extend_heap - increases heap by adding free block at the end of size 'words'
 */
static void *extend_heap(size_t words)
{
    char *ptr;
    size_t size;

    /* allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    /* min block size is 16 bytes */
    if (size < 16)
        size = 16;

    /* allocation for more space, also checking an extreme case */
    if ((int)(ptr = mem_sbrk(size)) == -1)
        return NULL;

    /* initialize free block header/footer and the epilogue header */
    PUT(HDRP(ptr), PACK(size, 0));     /* free block header */
    PUT(FTRP(ptr), PACK(size, 0));     /* free block footer */
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); /* new epilogue header */

    /* coalesce if the previous block was free */
    return coalesce(ptr);
}

/*
 * find_fit - find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
    if(free_blocks == 0)
        return NULL;
    /* first-fit search */
    void *ptr;
    for (ptr = free_list; GET_ALLOC(HDRP(ptr)) == 0; ptr = NEXT_PTR(ptr)) {
        if (asize <= GET_SIZE(HDRP(ptr)))
            return ptr; /* if a fit is found, return a pointer to that block, otherwise return NULL */
    }
    return NULL;
}

/*
 * add_to_freelist - sets the new block of the free list (ptr) to the first of the list
 */
static void add_to_freelist(void *ptr)
{
    NEXT_PTR(ptr) = free_list;
    PREV_PTR(free_list) = ptr;
    PREV_PTR(ptr) = NULL;
    free_list = ptr;
    free_blocks++;
}

/*
 * remove_from_freelist - removes the block (ptr) from the free list and adjusts pointers
 */
static void remove_from_freelist(void *ptr)
{
    if (PREV_PTR(ptr) == 0)
        free_list = NEXT_PTR(ptr);
    else
        NEXT_PTR(PREV_PTR(ptr)) = NEXT_PTR(ptr);
    PREV_PTR(NEXT_PTR(ptr)) = PREV_PTR(ptr);
    free_blocks--;
}

/*
 * mm_check - checks:
 *      Is every block in the free list marked as free?
 *      Are there any contiguous free blocks that somehow escaped coalescing?
 *      Is every free block actually in the free list?
 *      Do the pointers in the free list point to valid free blocks?
 *      Do any allocated blocks overlap?
 *      Do the pointers in a heap block point to valid heap addresses?
 */
static int mm_check(void)
{
    if (hc_valid() == 0 || hc_overlap() == 0 || hc_coalesce() == 0 || hc_freelist() == 0)
        return 0;
    return 1;
}

/*
 * mm_valid - checks if all pointers are within the heap and aligned by 8
 */
static int hc_valid(void)
{
    char *heap_checker;
    // loop goes through heap from heap_listp to epilogue, checking that each header is less than the next block
    // and the head of each pointer is less than the epilogue block
    for (heap_checker = NEXT_BLKP(heap_listp); heap_checker < epilogue; heap_checker = NEXT_BLKP(heap_checker)) {
        if (HDRP(heap_checker) < HDRP(NEXT_BLKP(heap_checker)) || (char*)GET(HDRP(heap_checker)) > epilogue) {
            printf("error in hc_valid - this block is not a valid address in heap: %p\n", heap_checker);
            return 0;
        }
    }
    return 1;
}

/*
 * hc_overlap - goes through entire heap and checks to see if any allocated blocks overlap
 */
static int hc_overlap(void)
{
    char *curr_ptr = heap_listp;
    while (curr_ptr != NULL && GET(HDRP(curr_ptr)) != 0) {
        if (GET_ALLOC(HDRP(curr_ptr))) { // if current pointer is allocated
            // and the current pointer + the size overlaps with the next pointer
            if (curr_ptr + GET_SIZE(HDRP(curr_ptr)) - WSIZE >= NEXT_PTR(curr_ptr)) {
                printf("error in hc_overlap - overlap at: %p\n", curr_ptr);
                return 0;
            }
        }
        curr_ptr = NEXT_BLKP(curr_ptr);
    }
    return 1;
}

/*
 * hc_coalesce - goes through free list and makes sure no blocks escaped coalescing
 */
static int hc_coalesce(void)
{
    void *curr_ptr = free_list;
    int count;
    for (count = 0; count < free_blocks; count++) {
        if (GET_ALLOC(HDRP(curr_ptr)) || GET_ALLOC(FTRP(curr_ptr))) { // if either the header or footer is allocated and did not escape coalesce
            printf("error in hc_coalesce - either the header or footer is allocated at: %p\n", curr_ptr);
            return 0;
        }
        if (NEXT_BLKP(curr_ptr) != 0 && !GET_ALLOC(HDRP(NEXT_BLKP(curr_ptr)))) { // checks if it has a next block and it is free
            printf("error in hc_coalesce - there is a next free block at: %p\n", curr_ptr);
            return 0;
        }
        if (PREV_BLKP(curr_ptr + WSIZE) != 0 && !GET_ALLOC(HDRP(PREV_BLKP(curr_ptr)))) { // checks if it has a previous block and it is free
            printf("error in hc_coalesce - there is a previous free block at: %p\n", curr_ptr);
            return 0;
        }
        curr_ptr = (char*)GET(curr_ptr + WSIZE);
    }
    return 1;
}

/*
 * hc_freelist - checks that every free block in heap is in the free list
 */
static int hc_freelist(void)
{
    void *curr_ptr = heap_listp;
    while (curr_ptr != NULL && GET_SIZE(HDRP(curr_ptr)) != 0) {
        if (GET_ALLOC(HDRP(curr_ptr)) == 0) {
            void *free_blk = free_list;
            while (curr_ptr != free_blk) { // searches free list for free block found in heap
                free_blk = (char*)GET(free_blk+WSIZE);
                if (free_blk == 0) { // reaches end of free list
                    printf("error in hc_freelist - this block is not in the free list %p\n", curr_ptr);
                    return 0;
                }
            }
        }
        curr_ptr = NEXT_BLKP(curr_ptr);
    }
    return 1;
}
