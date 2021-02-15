//
// -- An A* pathfinder inspired by the excellent tutorial at Red Blob Games --
//
// See:
//     https://www.redblobgames.com/pathfinding/a-star/introduction.html

#include <ctl/string.h>
#include <stdio.h>

typedef struct
{
    int x;
    int y;
    int priorty;
    int width;
} point;

point point_init(int x, int y, int width)
{
    return (point){x, y, 0, width};
}

int point_compare_priority(point *a, point *b)
{
    return a->priorty < b->priorty;
}

int point_equal(point *a, point *b)
{
    return a->x == b->x && a->y == b->y;
}

point point_from(str *maze, const char *c, int width)
{
    int index = str_find(maze, c);
    return point_init(index % width, index / width, width);
}

int point_index(point *p)
{
    return p->x + p->width * p->y;
}

int point_key_compare(point *a, point *b)
{
    int i = point_index(a);
    int j = point_index(b);
    return (i == j) ? 0 : (i < j) ? -1 : 1;
}

typedef struct
{
    point p;
    int i;
} pi;

typedef struct
{
    point a;
    point b;
} pp;

int pp_key_compare(pp *a, pp *b)
{
    return point_key_compare(&a->a, &b->a);
}

int pi_key_compare(pi *a, pi *b)
{
    return point_key_compare(&a->p, &b->p);
}

#define POD
#define NOT_INTEGRAL
#define T point
#include <ctl/priority_queue.h>

#define POD
#define NOT_INTEGRAL
#define T point
#include <ctl/deque.h>

#define POD
#define NOT_INTEGRAL
#define T pi
#include <ctl/set.h>

#define POD
#define NOT_INTEGRAL
#define T pp
#include <ctl/set.h>

deq_point astar(str *maze, int width)
{
    point start = point_from(maze, "@", width);
    point goal = point_from(maze, "!", width);
    pqu_point front = pqu_point_init(point_compare_priority);
    pqu_point_push(&front, start);
    set_pp from = set_pp_init(pp_key_compare);
    set_pi costs = set_pi_init(pi_key_compare);
    set_pi_insert(&costs, (pi){start, 0});
    while (!pqu_point_empty(&front))
    {
        point current = *pqu_point_top(&front);
        pqu_point_pop(&front);
        if (point_equal(&current, &goal))
            break;
        point deltas[] = {
            {-1, +1, 0, width},
            {0, +1, 0, width},
            {1, +1, 0, width},
            {-1, 0, 0, width},
            /* ~ ~ ~ ~ ~ ~ ~ */ {1, 0, 0, width},
            {-1, -1, 0, width},
            {0, -1, 0, width},
            {1, -1, 0, width},
        };
        for (size_t i = 0; i < len(deltas); i++)
        {
            point delta = deltas[i];
            point next = point_init(current.x + delta.x, current.y + delta.y, width);
            int new_cost = set_pi_find(&costs, (pi){.p = current}).ref->i;
            if (maze->vector[point_index(&next)] != '#')
            {
                set_pi_it cost = set_pi_find(&costs, (pi){.p = next});
                if (set_pi_it_done(&cost) || new_cost < cost.ref->i)
                {
                    set_pi_insert(&costs, (pi){next, new_cost});
                    next.priorty = new_cost + abs(goal.x - next.x) + abs(goal.y - next.y);
                    pqu_point_push(&front, next);
                    set_pp_insert(&from, (pp){next, current});
                }
            }
        }
    }
    point current = goal;
    deq_point path = deq_point_init();
    while (!point_equal(&current, &start))
    {
        deq_point_push_front(&path, current);
        current = set_pp_find(&from, (pp){.a = current}).ref->b;
    }
    deq_point_push_front(&path, start);
    pqu_point_free(&front);
    set_pp_free(&from);
    set_pi_free(&costs);
    return path;
}

int main(void)
{
    str maze = str_init("#########################################################################\n"
                        "#   #               #               #           #                   #   #\n"
                        "#   #   #########   #   #####   #########   #####   #####   #####   # ! #\n"
                        "#               #       #   #           #           #   #   #       #   #\n"
                        "#########   #   #########   #########   #####   #   #   #   #########   #\n"
                        "#       #   #               #           #   #   #   #   #           #   #\n"
                        "#   #   #############   #   #   #########   #####   #   #########   #   #\n"
                        "#   #               #   #   #       #           #           #       #   #\n"
                        "#   #############   #####   #####   #   #####   #########   #   #####   #\n"
                        "#           #       #   #       #   #       #           #   #           #\n"
                        "#   #####   #####   #   #####   #   #########   #   #   #   #############\n"
                        "#       #       #   #   #       #       #       #   #   #       #       #\n"
                        "#############   #   #   #   #########   #   #####   #   #####   #####   #\n"
                        "#           #   #           #       #   #       #   #       #           #\n"
                        "#   #####   #   #########   #####   #   #####   #####   #############   #\n"
                        "#   #       #           #           #       #   #   #               #   #\n"
                        "#   #   #########   #   #####   #########   #   #   #############   #   #\n"
                        "#   #           #   #   #   #   #           #               #   #       #\n"
                        "#   #########   #   #   #   #####   #########   #########   #   #########\n"
                        "#   #       #   #   #           #           #   #       #               #\n"
                        "# @ #   #####   #####   #####   #########   #####   #   #########   #   #\n"
                        "#   #                   #           #               #               #   #\n"
                        "#########################################################################\n");
    int width = str_find(&maze, "\n") + 1;
    deq_point path = astar(&maze, width);
    foreach (deq_point, &path, it)
        maze.vector[point_index(it.ref)] = 'x';
    printf("%s", str_c_str(&maze));
    str_free(&maze);
    deq_point_free(&path);
}
