/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
    /* Team name */
    "ateam",
    /* First member's full name */
    "moranzcw",
    /* First member's email address */
    "moranzcw@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


#define WSIZE     4
#define DSIZE     8

// 每次扩展堆的块大小
#define INITCHUNKSIZE (1<<6)    // 64 bytes
#define CHUNKSIZE (1<<12)       // 4 kb

#define LISTMAX     16

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word into address p
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val))

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Read the size and allocated fields from address p
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// Pointer of header and footer
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// The next block pointer and the prev block pointer.
#define NEXT_BLK_PTR(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLK_PTR(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

// The successor free block pointer's pointer and the predecessor free block pointer's pointer in the free list.
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

// The successor free block pointer and the predecessor free block pointer.
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))


/* Data structure 

Allocated block:

                            31  30  29  ... 5   4   3   2   1   0
                            +-------------------------+-------+--+
    Header:                 |   Size of the block     |       | A|
        block pointer +-->  +-------------------------+-------+--+
                            |                                    |
                            |   Payload                          |
                            |                                    |
                            +------------------------------------+
                            |   Padding(optional)                |
                            +-------------------------+-------+--+
    Footer:                 |   Size of the block     |       | A|
                            +-------------------------+-------+--+

Free block:

                            31  30  29  ... 5   4   3   2   1   0
                            +-------------------------+-------+--+
    Header:                 |   size of the block     |       | A|
        block pointer +-->  +-------------------------+-------+--+
                            |   pointer to its predecessor       |
                            +------------------------------------+
                            |   pointer to its successor         |
                            +------------------------------------+
                            |                                    |
                            |   Payload                          |
                            |                                    |
                            +------------------------------------+
                            |   Padding(optional)                |
                            +-------------------------+-------+--+
    Footer:                 |   size of the block     |       | A|
                            +-------------------------+-------+--+


Heap:
                            31  30  29  ... 5   4   3   2   1   0
    Start of heap:          +-------------------------+-------+--+
                            |   0(Padding)            |       |  |
                            +-------------------------+-------+--+  <--+
                            |   8                     |       | A|     |
static char *heap_listp +-> +-------------------------+-------+--+     +--  Prologue block
                            |   8                     |       | A|     |
                            +-------------------------+-------+--+  <--+
                            |                                    |
                            |                                    |
                            |   Blocks                           |
                            |                                    |
                            |                                    |
                            +-------------------------+-------+--+  <--+
    Footer:                 |   0                     |       | A|     +--  Epilogue block
                            +-------------------------+-------+--+  <--+   

*/


// Segregated free lists
void* segregated_free_lists[LISTMAX];

// Extend the heap
static void* extend_heap(size_t size);
// Coalesce adjacent free block if exists
static void* coalesce(void *block_ptr);
// 在ptr所指向的free block块中allocate size大小的块，如果剩下的空间大于2*DWSIZE，则将其分离后放入Free list
static void* place(void *ptr, size_t size);
// 将ptr所指向的free block插入到分离空闲表中
static void insert_node(void *ptr);
// 将ptr所指向的块从分离空闲表中删除
static void delete_node(void *ptr);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{   
    char *heap; 

    /* 初始化分离空闲链表 */
    for (int i = 0; i < LISTMAX; i++)
    {
        segregated_free_lists[i] = NULL;
    }

    // Initialize the heap
    if ((long)(heap = mem_sbrk(4 * WSIZE)) == -1)
        return -1;

    // Padding for memory alignment
    PUT(heap, 0);
    // Prologue block
    PUT(heap + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap + (2 * WSIZE), PACK(DSIZE, 1));
    // Epilogue block
    PUT(heap + (3 * WSIZE), PACK(0, 1));

    // Extend the heap to INITCHUNKSIZE
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    if (size == 0)
        return NULL;
    // Memory alignment
    if (size <= DSIZE)
    {
        size = 2 * DSIZE;
    }
    else
    {
        size = ALIGN(size + DSIZE);
    }


    int listnumber = 0;
    size_t searchsize = size;
    void *ptr = NULL;

    while (listnumber < LISTMAX)
    {
        /* 寻找对应链 */
        if (((searchsize <= 1) && (segregated_free_lists[listnumber] != NULL)))
        {
            ptr = segregated_free_lists[listnumber];
            /* 在该链寻找大小合适的free块 */
            while ((ptr != NULL) && ((size > GET_SIZE(HDRP(ptr)))))
            {
                ptr = PRED(ptr);
            }
            /* 找到对应的free块 */
            if (ptr != NULL)
                break;
        }

        searchsize >>= 1;
        listnumber++;
    }

    /* 没有找到合适的free块，扩展堆 */
    if (ptr == NULL)
    {
        if ((ptr = extend_heap(MAX(size, CHUNKSIZE))) == NULL)
            return NULL;
    }

    /* 在free块中allocate size大小的块 */
    ptr = place(ptr, size);

    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    /* 插入分离空闲链表 */
    insert_node(ptr);
    /* 注意合并 */
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_block = ptr;
    int remainder;

    if (size == 0)
        return NULL;

    /* 内存对齐 */
    if (size <= DSIZE)
    {
        size = 2 * DSIZE;
    }
    else
    {
        size = ALIGN(size + DSIZE);
    }

    /* 如果size小于原来块的大小，直接返回原来的块 */
    if ((remainder = GET_SIZE(HDRP(ptr)) - size) >= 0)
    {
        return ptr;
    }
    /* 否则先检查地址连续下一个块是否为free块或者该块是堆的结束块，因为我们要尽可能利用相邻的free块，以此减小“external fragmentation” */
    else if (!GET_ALLOC(HDRP(NEXT_BLK_PTR(ptr))) || !GET_SIZE(HDRP(NEXT_BLK_PTR(ptr))))
    {
        /* 即使加上后面连续地址上的free块空间也不够，需要扩展块 */
        if ((remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLK_PTR(ptr))) - size) < 0)
        {
            if (extend_heap(MAX(-remainder, CHUNKSIZE)) == NULL)
                return NULL;
            remainder += MAX(-remainder, CHUNKSIZE);
        }

        /* 删除刚刚利用的free块并设置新块的头尾 */
        delete_node(NEXT_BLK_PTR(ptr));
        PUT(HDRP(ptr), PACK(size + remainder, 1));
        PUT(FTRP(ptr), PACK(size + remainder, 1));
    }
    /* 没有可以利用的连续free块，而且size大于原来的块，这时只能申请新的不连续的free块、复制原块内容、释放原块 */
    else
    {
        new_block = mm_malloc(size);
        memcpy(new_block, ptr, GET_SIZE(HDRP(ptr)));
        mm_free(ptr);
    }

    return new_block;
}



static void *extend_heap(size_t size)
{
    void *ptr;
    // Memory alignment
    size = ALIGN(size);
    // Extend the heap
    if ((ptr = mem_sbrk(size)) == (void *)-1)
        return NULL;

    // Set the header and the footer
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    // Set the epilogue block of the heap
    PUT(HDRP(NEXT_BLK_PTR(ptr)), PACK(0, 1));
    // Insert this new free block into the free lists
    insert_node(ptr);
    // If previous block is free, coalesce them
    return coalesce(ptr);
}

static void insert_node(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    int listnumber = 0;
    void *search_ptr = NULL;
    void *insert_ptr = NULL;

    // Find the corresponding free list for block
    while ((listnumber < LISTMAX - 1) && (size > 1))
    {
        size >>= 1;
        listnumber++;
    }

    // Find the insert position for block, keep free list in ascending order
    search_ptr = segregated_free_lists[listnumber];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr))))
    {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    }

    /* 循环后有四种情况 */
    if (search_ptr != NULL)
    {
        /* 1. ->xx->insert->xx 在中间插入*/
        if (insert_ptr != NULL)
        {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        }
        /* 2. [listnumber]->insert->xx 在开头插入，而且后面有之前的free块*/
        else
        {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[listnumber] = ptr;
        }
    }
    else
    {
        if (insert_ptr != NULL)
        { /* 3. ->xxxx->insert 在结尾插入*/
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        }
        else
        { /* 4. [listnumber]->insert 该链为空，这是第一次插入 */
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[listnumber] = ptr;
        }
    }
}

static void delete_node(void *ptr)
{
    int listnumber = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    /* 通过块的大小找到对应的链 */
    while ((listnumber < LISTMAX - 1) && (size > 1))
    {
        size >>= 1;
        listnumber++;
    }

    /* 根据这个块的情况分四种可能性 */
    if (PRED(ptr) != NULL)
    {
        /* 1. xxx-> ptr -> xxx */
        if (SUCC(ptr) != NULL)
        {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        }
        /* 2. [listnumber] -> ptr -> xxx */
        else
        {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[listnumber] = PRED(ptr);
        }
    }
    else
    {
        /* 3. [listnumber] -> xxx -> ptr */
        if (SUCC(ptr) != NULL)
        {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        }
        /* 4. [listnumber] -> ptr */
        else
        {
            segregated_free_lists[listnumber] = NULL;
        }
    }
}


static void *coalesce(void *block_ptr)
{
    _Bool prev_allocated_flag = GET_ALLOC(HDRP(PREV_BLK_PTR(block_ptr)));
    _Bool next_allocated_flag = GET_ALLOC(HDRP(NEXT_BLK_PTR(block_ptr)));
    size_t size = GET_SIZE(HDRP(block_ptr));
    // There are four situations

    // 1. The previous block and the next block are both allocated
    if (prev_allocated_flag && next_allocated_flag)
    {
        return block_ptr;
    }
    // 2. The preious block is allocated, but the next block is free
    else if (prev_allocated_flag && !next_allocated_flag)
    {
        // Delete current block and the next block
        delete_node(block_ptr);
        delete_node(NEXT_BLK_PTR(block_ptr));
        // Reset header and footer for the new block
        size += GET_SIZE(HDRP(NEXT_BLK_PTR(block_ptr)));
        PUT(HDRP(block_ptr), PACK(size, 0));
        PUT(FTRP(block_ptr), PACK(size, 0));
    }
    // 3. The previous block is free, but the next block is allocated
    else if (!prev_allocated_flag && next_allocated_flag)
    {
        // Delete the previous block and current block
        delete_node(PREV_BLK_PTR(block_ptr));
        delete_node(block_ptr);
        // Reset header and footer for the new block
        size += GET_SIZE(HDRP(PREV_BLK_PTR(block_ptr)));
        PUT(FTRP(block_ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLK_PTR(block_ptr)), PACK(size, 0));
        // Reset current block's pointer
        block_ptr = PREV_BLK_PTR(block_ptr);
    }
    // 4. The previous block and the next block are both free
    else
    {
        // Delete all three blocks
        delete_node(PREV_BLK_PTR(block_ptr));
        delete_node(block_ptr);
        delete_node(NEXT_BLK_PTR(block_ptr));
        // Reset header and footer for the new block
        size += GET_SIZE(HDRP(PREV_BLK_PTR(block_ptr))) + GET_SIZE(HDRP(NEXT_BLK_PTR(block_ptr)));
        PUT(HDRP(PREV_BLK_PTR(block_ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLK_PTR(block_ptr)), PACK(size, 0));
        // Reset current block's pointer
        block_ptr = PREV_BLK_PTR(block_ptr);
    }

    // Insert this new block into the free lists
    insert_node(block_ptr);

    return block_ptr;
}

static void *place(void *ptr, size_t size)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    /* allocate size大小的空间后剩余的大小 */
    size_t remainder = ptr_size - size;

    delete_node(ptr);

    /* 如果剩余的大小小于最小块，则不分离原块 */
    if (remainder < DSIZE * 2)
    {
        PUT(HDRP(ptr), PACK(ptr_size, 1));
        PUT(FTRP(ptr), PACK(ptr_size, 1));
    }

    /* 否则分离原块，但这里要注意这样一种情况（在binary-bal.rep和binary2-bal.rep有体现）： 
    *  如果每次allocate的块大小按照小、大、小、大的连续顺序来的话，我们的free块将会被“拆”成以下这种结构：
    *  其中s代表小的块，B代表大的块

 s      B      s       B     s      B      s     B
+--+----------+--+----------+-+-----------+-+---------+
|  |          |  |          | |           | |         |
|  |          |  |          | |           | |         |
|  |          |  |          | |           | |         |
+--+----------+--+----------+-+-----------+-+---------+

    *  这样看起来没什么问题，但是如果程序后来free的时候不是按照”小、大、小、大“的顺序来释放的话就会出现“external fragmentation”
    *  例如当程序将大的块全部释放了，但小的块依旧是allocated：

 s             s             s             s
+--+----------+--+----------+-+-----------+-+---------+
|  |          |  |          | |           | |         |
|  |   Free   |  |   Free   | |   Free    | |   Free  |
|  |          |  |          | |           | |         |
+--+----------+--+----------+-+-----------+-+---------+

    *  这样即使我们有很多free的大块可以使用，但是由于他们不是连续的，我们不能将它们合并，如果下一次来了一个大小为B+1的allocate请求
    *  我们就还需要重新去找一块Free块
    *  与此相反，如果我们根据allocate块的大小将小的块放在连续的地方，将达到开放在连续的地方：

 s  s  s  s  s  s      B            B           B
+--+--+--+--+--+--+----------+------------+-----------+
|  |  |  |  |  |  |          |            |           |
|  |  |  |  |  |  |          |            |           |
|  |  |  |  |  |  |          |            |           |
+--+--+--+--+--+--+----------+------------+-----------+

    *  这样即使程序连续释放s或者B，我们也能够合并free块，不会产生external fragmentation
    *  这里“大小”相对判断是根据binary-bal.rep和binary2-bal.rep这两个文件设置的，我这里在96附近能够达到最优值
    *  
    */
    else if (size >= 96)
    {
        PUT(HDRP(ptr), PACK(remainder, 0));
        PUT(FTRP(ptr), PACK(remainder, 0));
        PUT(HDRP(NEXT_BLK_PTR(ptr)), PACK(size, 1));
        PUT(FTRP(NEXT_BLK_PTR(ptr)), PACK(size, 1));
        insert_node(ptr);
        return NEXT_BLK_PTR(ptr);
    }

    else
    {
        PUT(HDRP(ptr), PACK(size, 1));
        PUT(FTRP(ptr), PACK(size, 1));
        PUT(HDRP(NEXT_BLK_PTR(ptr)), PACK(remainder, 0));
        PUT(FTRP(NEXT_BLK_PTR(ptr)), PACK(remainder, 0));
        insert_node(NEXT_BLK_PTR(ptr));
    }
    return ptr;
}











