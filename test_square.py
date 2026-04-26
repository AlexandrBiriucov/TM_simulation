"""
Food Delivery Simulation v2
Сетка улиц + маршрутизация по дорогам (BFS) + FSM
"""

import pygame
import math
import random
from collections import deque
from enum import Enum, auto
from typing import Optional, List, Tuple

# ══════════════════════════════════════════════════════
#  КОНФИГ
# ══════════════════════════════════════════════════════

WIDTH, HEIGHT = 1280, 780
FPS           = 60
SIDEBAR_W     = 270
SIM_W         = WIDTH - SIDEBAR_W
SIM_H         = HEIGHT

CELL          = 60          # размер клетки сетки (пикселей)
MARGIN        = 30          # отступ от края до первой дороги

# вычислим количество линий
COLS = (SIM_W - 2 * MARGIN) // CELL + 1   # вертикальные линии (x)
ROWS = (SIM_H - 2 * MARGIN) // CELL + 1   # горизонтальные линии (y)

NUM_COURIERS    = 6
NUM_RESTAURANTS = 4
NUM_CUSTOMERS   = 8       # активных клиентов одновременно
ORDER_INTERVAL  = 5.0     # секунд между новыми заказами
BASE_SPEED      = 110.0   # пикс/сек
ALPHA           = 0.6
PREP_MIN        = 3.0
PREP_MAX        = 8.0
SNAP_DIST       = 6       # радиус "добрался до узла"

# ══════════════════════════════════════════════════════
#  ЦВЕТА
# ══════════════════════════════════════════════════════

BG           = ( 10,  13,  20)
BLOCK_COL    = ( 22,  28,  38)   # квадраты-блоки
ROAD_COL     = ( 38,  45,  60)   # дороги
ROAD_LINE    = ( 55,  65,  85)   # разметка
CROSS_COL    = ( 48,  56,  75)   # перекрёстки
PANEL_BG     = ( 15,  19,  28)
PANEL_BORDER = ( 40,  50,  68)

C_REST    = (220,  55,  55)
C_CUST    = ( 45, 200,  95)
C_COURIER = ( 55, 145, 235)

C_TEXT   = (195, 208, 225)
C_LABEL  = ( 95, 118, 148)
C_ACCENT = ( 55, 178, 255)
C_WARN   = (255, 162,  40)
C_OK     = ( 45, 200,  95)

STATE_COL = {
    "IDLE":          ( 75,  88, 108),
    "TO_RESTAURANT": (255, 158,  38),
    "PICKUP":        (195,  75, 200),
    "TO_CUSTOMER":   ( 55, 178, 255),
}
ORDER_COL = {
    "WAITING":   (175, 175,  55),
    "PREPARING": (215,  95,  38),
    "READY":     ( 75, 198,  75),
    "DELIVERED": ( 60,  60,  60),
}

# ══════════════════════════════════════════════════════
#  СЕТКА УЛИЦ
# ══════════════════════════════════════════════════════

def node_pos(col: int, row: int) -> Tuple[int, int]:
    """Пиксельные координаты перекрёстка (col, row)."""
    return (MARGIN + col * CELL, MARGIN + row * CELL)

def nearest_node(px: float, py: float) -> Tuple[int, int]:
    """Ближайший перекрёсток к пиксельной точке."""
    col = round((px - MARGIN) / CELL)
    row = round((py - MARGIN) / CELL)
    col = max(0, min(COLS - 1, col))
    row = max(0, min(ROWS - 1, row))
    return (col, row)

def bfs_path(start: Tuple[int,int], end: Tuple[int,int]) -> List[Tuple[int,int]]:
    """BFS по сетке, возвращает список пиксельных точек от start до end."""
    if start == end:
        return [node_pos(*start)]
    visited = {start: None}
    q = deque([start])
    while q:
        cur = q.popleft()
        if cur == end:
            break
        cx, cy = cur
        for nx, ny in [(cx+1,cy),(cx-1,cy),(cx,cy+1),(cx,cy-1)]:
            if 0 <= nx < COLS and 0 <= ny < ROWS and (nx,ny) not in visited:
                visited[(nx,ny)] = cur
                q.append((nx,ny))
    # восстановить путь
    path = []
    node = end
    while node is not None:
        path.append(node_pos(*node))
        node = visited.get(node)
    path.reverse()
    return path

def random_node() -> Tuple[int, int]:
    return (random.randint(0, COLS-1), random.randint(0, ROWS-1))

# ══════════════════════════════════════════════════════
#  МАТЕМАТИКА
# ══════════════════════════════════════════════════════

def dist(a, b) -> float:
    return math.hypot(a[0]-b[0], a[1]-b[1])

def norm(dx, dy):
    d = math.hypot(dx, dy)
    return (dx/d, dy/d) if d > 0.001 else (0.0, 0.0)

def traffic_factor(sim_time: float, weather: float) -> float:
    hour = (sim_time / 60.0) % 24
    rush = 0.6*(math.exp(-((hour-8)**2)/2) + math.exp(-((hour-18)**2)/2))
    return rush + weather

def effective_speed(sim_time: float, weather: float) -> float:
    c = traffic_factor(sim_time, weather)
    return BASE_SPEED / (1.0 + ALPHA * c)

# ══════════════════════════════════════════════════════
#  ENUM
# ══════════════════════════════════════════════════════

class CourierState(Enum):
    IDLE          = auto()
    TO_RESTAURANT = auto()
    PICKUP        = auto()
    TO_CUSTOMER   = auto()

class OrderState(Enum):
    WAITING   = auto()
    PREPARING = auto()
    READY     = auto()
    DELIVERED = auto()

# ══════════════════════════════════════════════════════
#  АГЕНТЫ
# ══════════════════════════════════════════════════════

_uid = 0
def uid():
    global _uid; _uid += 1; return _uid

# ── Ресторан ──────────────────────────────────────────

class Restaurant:
    def __init__(self):
        node = random_node()
        self.node = node
        self.pos  = node_pos(*node)
        self.id   = uid()

    def draw(self, surf, font):
        x, y = self.pos
        pygame.draw.rect(surf, C_REST, (x-12, y-12, 24, 24), border_radius=4)
        pygame.draw.rect(surf, (255,110,110), (x-12, y-12, 24, 24), 2, border_radius=4)
        lbl = font.render("R", True, (255,255,255))
        surf.blit(lbl, (x - lbl.get_width()//2, y - lbl.get_height()//2))

# ── Клиент ────────────────────────────────────────────

class Customer:
    def __init__(self):
        self._relocate()
        self.id         = uid()
        self.flash      = 0.0
        self.active     = True   # виден на карте пока ждёт

    def _relocate(self):
        node = random_node()
        self.node = node
        self.pos  = node_pos(*node)

    def draw(self, surf, font):
        if not self.active:
            return
        x, y = self.pos
        alpha = min(1.0, self.flash / 0.5) if self.flash > 0 else 0
        col = (
            int(C_CUST[0] + (255-C_CUST[0])*(1-alpha)),
            int(C_CUST[1] + (255-C_CUST[1])*(1-alpha)),
            int(C_CUST[2] + (255-C_CUST[2])*(1-alpha)),
        ) if alpha > 0 else C_CUST
        pygame.draw.circle(surf, col, (x, y), 10)
        pygame.draw.circle(surf, (110, 255, 155), (x, y), 10, 2)
        lbl = font.render("C", True, (255,255,255))
        surf.blit(lbl, (x - lbl.get_width()//2, y - lbl.get_height()//2))

    def update(self, dt):
        if self.flash > 0:
            self.flash = max(0.0, self.flash - dt)

# ── Заказ ─────────────────────────────────────────────

class Order:
    def __init__(self, restaurant: Restaurant, customer: Customer, sim_time: float):
        self.id         = uid()
        self.restaurant = restaurant
        self.customer   = customer
        self.state      = OrderState.WAITING
        self.state_name = "WAITING"
        self.prep_time  = random.uniform(PREP_MIN, PREP_MAX)
        self.prep_done  = 0.0
        self.created_at = sim_time
        self.delivered_at: Optional[float] = None

    def update(self, dt):
        if self.state == OrderState.PREPARING:
            self.prep_done += dt
            if self.prep_done >= self.prep_time:
                self.state      = OrderState.READY
                self.state_name = "READY"

    def assign(self):
        if self.state == OrderState.WAITING:
            self.state      = OrderState.PREPARING
            self.state_name = "PREPARING"

    def deliver(self, sim_time):
        self.state         = OrderState.DELIVERED
        self.state_name    = "DELIVERED"
        self.delivered_at  = sim_time

# ── Курьер ────────────────────────────────────────────

class Courier:
    def __init__(self, cid: int):
        node = random_node()
        self.id    = cid
        self.node  = node
        self.pos   = list(node_pos(*node))  # float list

        self.state      = CourierState.IDLE
        self.state_name = "IDLE"
        self.order: Optional[Order] = None

        # маршрут: список пиксельных точек (waypoints)
        self.path: List[Tuple[int,int]] = []
        self.path_idx = 0

        self.speed     = 0.0
        self.trail: List[Tuple[float,float]] = []
        self.trail_t   = 0.0
        self.pulse     = 0.0
        self.total_del = 0
        self.total_km  = 0.0

    # ── FSM ────────────────────────────────────────

    def assign_order(self, order: Order):
        """IDLE → TO_RESTAURANT"""
        self.order      = order
        self.state      = CourierState.TO_RESTAURANT
        self.state_name = "TO_RESTAURANT"
        self._set_path_to(order.restaurant.node)
        order.assign()

    def _arrive_restaurant(self):
        """TO_RESTAURANT → PICKUP"""
        self.state      = CourierState.PICKUP
        self.state_name = "PICKUP"
        self.path       = []

    def _pickup_ready(self):
        """PICKUP → TO_CUSTOMER"""
        self.state      = CourierState.TO_CUSTOMER
        self.state_name = "TO_CUSTOMER"
        self._set_path_to(self.order.customer.node)

    def _deliver(self, sim_time: float, on_deliver_cb):
        """TO_CUSTOMER → IDLE"""
        self.order.deliver(sim_time)
        on_deliver_cb(self.order)
        self.total_del += 1
        self.order      = None
        self.state      = CourierState.IDLE
        self.state_name = "IDLE"
        self.path       = []

    def _set_path_to(self, target_node: Tuple[int,int]):
        cur_node = nearest_node(self.pos[0], self.pos[1])
        self.path     = bfs_path(cur_node, target_node)
        self.path_idx = 0

    # ── Движение ────────────────────────────────────

    def update(self, dt: float, sim_time: float, weather: float, on_deliver_cb):
        self.speed = effective_speed(sim_time, weather)
        self.pulse = (self.pulse + dt * 3) % (2 * math.pi)

        # trail
        self.trail_t += dt
        if self.trail_t > 0.10:
            self.trail_t = 0.0
            self.trail.append((self.pos[0], self.pos[1]))
            if len(self.trail) > 20:
                self.trail.pop(0)

        # движение по path
        if self.path and self.path_idx < len(self.path):
            tx, ty = self.path[self.path_idx]
            dx, dy = tx - self.pos[0], ty - self.pos[1]
            step   = self.speed * dt
            d      = math.hypot(dx, dy)
            if d < SNAP_DIST:
                self.pos[0] = float(tx)
                self.pos[1] = float(ty)
                self.path_idx += 1
            else:
                nx, ny = norm(dx, dy)
                move   = min(step, d)
                self.pos[0] += nx * move
                self.pos[1] += ny * move
                self.total_km += move

        # FSM переходы
        at_end = (not self.path) or (self.path_idx >= len(self.path))

        if self.state == CourierState.TO_RESTAURANT and at_end:
            self._arrive_restaurant()

        elif self.state == CourierState.PICKUP:
            if self.order and self.order.state == OrderState.READY:
                self._pickup_ready()

        elif self.state == CourierState.TO_CUSTOMER and at_end:
            self._deliver(sim_time, on_deliver_cb)

    # ── Рисование ───────────────────────────────────

    def draw(self, surf, font_xs):
        x, y = int(self.pos[0]), int(self.pos[1])
        col  = STATE_COL.get(self.state_name, C_COURIER)

        # trail
        for i, (tx, ty) in enumerate(self.trail):
            r = max(1, int(3 * i / max(len(self.trail),1)))
            faded = tuple(int(c * (i / max(len(self.trail),1)) * 0.55) for c in col)
            pygame.draw.circle(surf, faded, (int(tx), int(ty)), r)

        # линия к цели (если едет к клиенту)
        if self.state == CourierState.TO_CUSTOMER and self.order:
            cx2, cy2 = self.order.customer.pos
            line_s = pygame.Surface((SIM_W, SIM_H), pygame.SRCALPHA)
            pygame.draw.line(line_s, (255, 200, 50, 35), (x, y), (cx2, cy2), 1)
            surf.blit(line_s, (0,0))

        # пульсирующее кольцо
        pr = int(15 + 4 * math.sin(self.pulse))
        pygame.draw.circle(surf, col, (x, y), pr, 1)

        # тело
        pygame.draw.circle(surf, col, (x, y), 10)
        pygame.draw.circle(surf, (200, 225, 255), (x, y), 10, 2)

        # номер
        lbl = font_xs.render(str(self.id), True, (255,255,255))
        surf.blit(lbl, (x - lbl.get_width()//2, y - lbl.get_height()//2))

        # статус над головой
        if self.state != CourierState.IDLE:
            short = {"TO_RESTAURANT":"→REST","PICKUP":"WAIT","TO_CUSTOMER":"→CUST"}.get(self.state_name,"")
            slbl  = font_xs.render(short, True, col)
            surf.blit(slbl, (x - slbl.get_width()//2, y - 22))

# ══════════════════════════════════════════════════════
#  ДИСПЕТЧЕР
# ══════════════════════════════════════════════════════

class Dispatcher:
    @staticmethod
    def assign(couriers: List[Courier], orders: List[Order]):
        pending = [o for o in orders if o.state == OrderState.WAITING]
        idle    = [c for c in couriers if c.state == CourierState.IDLE]
        for order in pending:
            if not idle:
                break
            # ближайший свободный курьер к ресторану
            best = min(idle, key=lambda c: dist(c.pos, order.restaurant.pos))
            best.assign_order(order)
            idle.remove(best)

# ══════════════════════════════════════════════════════
#  СИМУЛЯЦИЯ
# ══════════════════════════════════════════════════════

class Simulation:
    def __init__(self):
        self.sim_time     = 0.0
        self.weather      = random.uniform(0.0, 0.35)
        self.weather_tmr  = 30.0
        self.order_tmr    = 0.0
        self.delivered_count = 0
        self.avg_del_time = 0.0
        self._del_times: List[float] = []

        # фиксированные рестораны
        self.restaurants: List[Restaurant] = []
        used_nodes = set()
        while len(self.restaurants) < NUM_RESTAURANTS:
            r = Restaurant()
            if r.node not in used_nodes:
                used_nodes.add(r.node)
                self.restaurants.append(r)

        # активные клиенты
        self.customers: List[Customer] = []
        for _ in range(NUM_CUSTOMERS):
            self._spawn_customer(used_nodes)

        # курьеры
        self.couriers: List[Courier] = [Courier(i+1) for i in range(NUM_COURIERS)]

        # активные (недоставленные) заказы
        self.orders: List[Order] = []

    def _spawn_customer(self, used=None):
        if used is None:
            used = {r.node for r in self.restaurants}
        c = Customer()
        # не ставить на перекрёсток ресторана
        attempts = 0
        while c.node in used and attempts < 50:
            c._relocate(); attempts += 1
        self.customers.append(c)

    def _spawn_order(self):
        # берём случайного клиента без активного заказа
        free_customers = [
            c for c in self.customers
            if c.active and not any(o.customer is c for o in self.orders)
        ]
        if not free_customers:
            return
        r = random.choice(self.restaurants)
        c = random.choice(free_customers)
        o = Order(r, c, self.sim_time)
        self.orders.append(o)

    def _on_deliver(self, order: Order):
        """Коллбэк: заказ доставлен → клиент исчезает, появляется новый."""
        customer = order.customer
        customer.flash = 1.5

        # через 0 сек убираем и пересоздаём (делаем сразу)
        dt_time = order.delivered_at - order.created_at
        self._del_times.append(dt_time)
        self.avg_del_time = sum(self._del_times) / len(self._del_times)
        self.delivered_count += 1

        # убираем клиента
        customer.active = False
        if customer in self.customers:
            self.customers.remove(customer)

        # новый клиент на случайном перекрёстке
        self._spawn_customer()

    def update(self, dt: float):
        self.sim_time += dt

        # погода
        self.weather_tmr -= dt
        if self.weather_tmr <= 0:
            self.weather = max(0.0, min(1.0, self.weather + random.uniform(-0.2, 0.2)))
            self.weather_tmr = random.uniform(20.0, 50.0)

        # новые заказы
        self.order_tmr += dt
        if self.order_tmr >= ORDER_INTERVAL:
            self.order_tmr = 0.0
            self._spawn_order()

        # диспетчер
        Dispatcher.assign(self.couriers, self.orders)

        # обновляем заказы
        for o in self.orders:
            o.update(dt)

        # обновляем клиентов
        for c in self.customers:
            c.update(dt)

        # обновляем курьеров
        for courier in self.couriers:
            courier.update(dt, self.sim_time, self.weather, self._on_deliver)

        # чистим доставленные заказы из списка
        self.orders = [o for o in self.orders if o.state != OrderState.DELIVERED]

    @property
    def active_orders(self):
        return self.orders   # уже только недоставленные

    @property
    def system_load(self):
        return len(self.orders) / max(NUM_COURIERS, 1)

    @property
    def simulated_hour(self):
        return (self.sim_time / 60.0) % 24

# ══════════════════════════════════════════════════════
#  РЕНДЕРЕР
# ══════════════════════════════════════════════════════

class Renderer:
    def __init__(self, screen):
        self.screen   = screen
        self.sim_surf = pygame.Surface((SIM_W, SIM_H))
        self.f_big  = pygame.font.SysFont("consolas", 20, bold=True)
        self.f_med  = pygame.font.SysFont("consolas", 13, bold=True)
        self.f_sm   = pygame.font.SysFont("consolas", 11)
        self.f_xs   = pygame.font.SysFont("consolas",  9)
        self.f_icon = pygame.font.SysFont("consolas",  9, bold=True)

    # ── Сетка ────────────────────────────────────────

    def _draw_city(self):
        s = self.sim_surf
        s.fill(BG)

        # заливаем блоки (квадраты между дорогами)
        for col in range(COLS - 1):
            for row in range(ROWS - 1):
                x1, y1 = node_pos(col,   row)
                x2, y2 = node_pos(col+1, row+1)
                road_w = 10
                rx = x1 + road_w // 2
                ry = y1 + road_w // 2
                rw = x2 - x1 - road_w
                rh = y2 - y1 - road_w
                pygame.draw.rect(s, BLOCK_COL, (rx, ry, rw, rh))

        # дороги (горизонтальные полосы)
        for row in range(ROWS):
            x1, y = node_pos(0,      row)
            x2, _ = node_pos(COLS-1, row)
            pygame.draw.line(s, ROAD_COL, (x1, y), (x2, y), 10)
            # пунктирная разметка
            for dx in range(0, x2 - x1, 20):
                pygame.draw.line(s, ROAD_LINE, (x1+dx, y), (x1+dx+10, y), 1)

        # дороги (вертикальные)
        for col in range(COLS):
            x, y1 = node_pos(col, 0)
            _, y2  = node_pos(col, ROWS-1)
            pygame.draw.line(s, ROAD_COL, (x, y1), (x, y2), 10)
            for dy in range(0, y2 - y1, 20):
                pygame.draw.line(s, ROAD_LINE, (x, y1+dy), (x, y1+dy+10), 1)

        # перекрёстки
        for col in range(COLS):
            for row in range(ROWS):
                x, y = node_pos(col, row)
                pygame.draw.rect(s, CROSS_COL, (x-5, y-5, 10, 10))

    # ── Сайдбар ───────────────────────────────────────

    def _draw_sidebar(self, sim: Simulation):
        sx = SIM_W
        pygame.draw.rect(self.screen, PANEL_BG, (sx, 0, SIDEBAR_W, HEIGHT))
        pygame.draw.line(self.screen, PANEL_BORDER, (sx, 0), (sx, HEIGHT), 1)

        y = 14
        def txt(msg, col=C_TEXT, f=None):
            nonlocal y
            fo = f or self.f_sm
            s  = fo.render(msg, True, col)
            self.screen.blit(s, (sx+12, y))
            y += s.get_height() + 3

        def sep(h=8):
            nonlocal y
            y += h // 2
            pygame.draw.line(self.screen, PANEL_BORDER, (sx+8, y), (sx+SIDEBAR_W-8, y), 1)
            y += h // 2

        def bar(label, val, maxv, color):
            nonlocal y
            txt(label, C_LABEL)
            bw, bh = SIDEBAR_W - 24, 7
            pygame.draw.rect(self.screen, (28,36,50), (sx+12, y, bw, bh), border_radius=3)
            fill = int(bw * min(val / max(maxv,0.001), 1.0))
            if fill > 0:
                pygame.draw.rect(self.screen, color, (sx+12, y, fill, bh), border_radius=3)
            y += bh + 5

        txt("FOOD DELIVERY", C_ACCENT, self.f_big)
        txt("SIMULATION v2", C_ACCENT, self.f_med)
        sep(10)

        # время
        h    = sim.simulated_hour
        hh   = int(h); mm = int((h-hh)*60)
        txt(f"Время   {hh:02d}:{mm:02d}", C_TEXT, self.f_med)
        wstr = "Ясно" if sim.weather < 0.2 else ("Дождь" if sim.weather > 0.5 else "Облачно")
        txt(f"Погода  {wstr}", C_TEXT)
        rush = traffic_factor(sim.sim_time, sim.weather)
        bar("Пробки", rush, 1.5, C_WARN)
        spd = effective_speed(sim.sim_time, sim.weather)
        txt(f"Скорость  {spd:.0f} пкс/с", C_LABEL)
        sep()

        txt("ЗАКАЗЫ", C_ACCENT, self.f_med)
        txt(f"Активных       {len(sim.active_orders)}", C_TEXT)
        txt(f"Доставлено     {sim.delivered_count}", C_OK)
        txt(f"Ср. время      {sim.avg_del_time:.1f}с", C_LABEL)
        bar("Нагрузка", sim.system_load, 3.0, C_WARN)
        sep()

        txt("КУРЬЕРЫ", C_ACCENT, self.f_med)
        for c in sim.couriers:
            sc    = STATE_COL.get(c.state_name, C_COURIER)
            short = c.state_name.replace("_"," ")
            line  = self.f_xs.render(f"#{c.id}  {short:<16}", True, sc)
            self.screen.blit(line, (sx+12, y))
            d_lbl = self.f_xs.render(f"x{c.total_del}", True, C_LABEL)
            self.screen.blit(d_lbl, (sx+SIDEBAR_W-d_lbl.get_width()-12, y))
            y += line.get_height() + 2
        sep()

        txt("ОЧЕРЕДЬ", C_ACCENT, self.f_med)
        for o in sim.active_orders[-9:]:
            sc  = ORDER_COL.get(o.state_name, C_TEXT)
            age = sim.sim_time - o.created_at
            msg = self.f_xs.render(f"#{o.id:<3} {o.state_name:<10} {age:4.0f}с", True, sc)
            self.screen.blit(msg, (sx+12, y))
            y += msg.get_height() + 2
        sep(12)

        # легенда
        txt("ЛЕГЕНДА", C_ACCENT, self.f_med)
        items = [(C_REST,"Ресторан"), (C_CUST,"Клиент"), (C_COURIER,"Курьер")]
        for col2, lbl in items:
            pygame.draw.circle(self.screen, col2, (sx+20, y+5), 6)
            t = self.f_xs.render(lbl, True, C_TEXT)
            self.screen.blit(t, (sx+32, y))
            y += 14

    # ── Главный рендер ────────────────────────────────

    def render(self, sim: Simulation, speed_mult: float, paused: bool):
        self._draw_city()

        # рестораны
        for r in sim.restaurants:
            r.draw(self.sim_surf, self.f_icon)

        # клиенты
        for c in sim.customers:
            c.draw(self.sim_surf, self.f_icon)

        # курьеры
        for courier in sim.couriers:
            courier.draw(self.sim_surf, self.f_xs)

        self.screen.blit(self.sim_surf, (0, 0))
        self._draw_sidebar(sim)

        # HUD
        hints = [
            f"SPACE=пауза  UP/DOWN=скорость({speed_mult:.1f}x)  R=сброс  ESC=выход",
            f"{'⏸ ПАУЗА' if paused else '▶ РАБОТАЕТ'}  |  sim: {sim.sim_time:.1f}с",
        ]
        for i, h in enumerate(hints):
            s = self.f_xs.render(h, True, (70, 90, 120))
            self.screen.blit(s, (6, HEIGHT - 22 + i * 12))

        pygame.display.flip()

# ══════════════════════════════════════════════════════
#  MAIN
# ══════════════════════════════════════════════════════

def main():
    pygame.init()
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Food Delivery Simulation v2 — Улицы + FSM")
    clock  = pygame.time.Clock()

    sim      = Simulation()
    renderer = Renderer(screen)

    paused     = False
    speed_mult = 1.0

    running = True
    while running:
        dt_real = clock.tick(FPS) / 1000.0
        dt      = dt_real * speed_mult

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.KEYDOWN:
                if   event.key == pygame.K_ESCAPE: running = False
                elif event.key == pygame.K_SPACE:  paused = not paused
                elif event.key == pygame.K_UP:     speed_mult = min(speed_mult * 1.5, 8.0)
                elif event.key == pygame.K_DOWN:   speed_mult = max(speed_mult / 1.5, 0.25)
                elif event.key == pygame.K_r:
                    sim = Simulation()

        if not paused:
            sim.update(dt)

        renderer.render(sim, speed_mult, paused)

    pygame.quit()

if __name__ == "__main__":
    main()