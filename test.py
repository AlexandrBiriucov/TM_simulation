"""
Food Delivery Simulation
Agent-Based Model with Finite State Machines
Uses: Python + Pygame
"""

import pygame
import math
import random
import time
from enum import Enum, auto
from dataclasses import dataclass, field
from typing import Optional, List, Tuple

# ─────────────────────────────────────────────
#  CONFIGURATION
# ─────────────────────────────────────────────

WIDTH, HEIGHT = 1280, 780
FPS = 60
SIDEBAR_W = 280

SIM_W = WIDTH - SIDEBAR_W          # simulation canvas width
SIM_H = HEIGHT

NUM_COURIERS = 5
NUM_RESTAURANTS = 4
NUM_CUSTOMERS = 10

BASE_SPEED = 90.0                   # pixels / second
ALPHA = 0.6                         # traffic sensitivity
ORDER_INTERVAL = 4.0                # seconds between new orders
PREP_TIME_MIN = 3.0                 # restaurant prep time range (s)
PREP_TIME_MAX = 8.0
PICKUP_RADIUS = 18
DELIVERY_RADIUS = 18

# ─────────────────────────────────────────────
#  COLOUR PALETTE  (dark industrial theme)
# ─────────────────────────────────────────────

BG          = (14,  17,  23)
GRID_COL    = (22,  28,  38)
PANEL_BG    = (18,  22,  30)
PANEL_BORDER= (38,  48,  64)

C_REST      = (220,  60,  60)       # restaurants  – red
C_CUST      = ( 50, 200, 100)       # customers    – green
C_COURIER   = ( 60, 140, 230)       # couriers     – blue
C_IDLE      = ( 80,  80, 100)       # idle courier overlay
C_ORDER_LINE= (255, 200,  50, 80)   # delivery line (with alpha)

C_TEXT      = (200, 210, 225)
C_LABEL     = (100, 120, 150)
C_ACCENT    = ( 60, 180, 255)
C_WARN      = (255, 160,  40)
C_OK        = ( 50, 200, 100)

STATE_COLORS = {
    "IDLE":          ( 80,  90, 110),
    "TO_RESTAURANT": (255, 160,  40),
    "PICKUP":        (200,  80, 200),
    "TO_CUSTOMER":   ( 60, 180, 255),
}

ORDER_STATE_COLORS = {
    "WAITING":    (180, 180,  60),
    "PREPARING":  (220, 100,  40),
    "READY":      ( 80, 200,  80),
    "DELIVERED":  ( 80,  80,  80),
}

# ─────────────────────────────────────────────
#  ENUMS
# ─────────────────────────────────────────────

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

# ─────────────────────────────────────────────
#  HELPERS
# ─────────────────────────────────────────────

def dist(a: Tuple[float,float], b: Tuple[float,float]) -> float:
    return math.hypot(a[0]-b[0], a[1]-b[1])

def norm(dx: float, dy: float) -> Tuple[float,float]:
    d = math.hypot(dx, dy)
    return (dx/d, dy/d) if d > 0 else (0.0, 0.0)

def traffic_factor(sim_time: float, weather: float) -> float:
    """c(t) = time_factor + weather_factor"""
    hour = (sim_time / 60.0) % 24          # simulated hour (1 sim-min = 1 hour)
    # rush hours ~ 7-9 and 17-19
    rush = 0.6 * (math.exp(-((hour-8)**2)/2) + math.exp(-((hour-18)**2)/2))
    return rush + weather

def effective_speed(sim_time: float, weather: float) -> float:
    """v(t) = v0 / (1 + α * c(t))"""
    c = traffic_factor(sim_time, weather)
    return BASE_SPEED / (1.0 + ALPHA * c)

# ─────────────────────────────────────────────
#  AGENTS
# ─────────────────────────────────────────────

_id_counter = 0
def next_id() -> int:
    global _id_counter
    _id_counter += 1
    return _id_counter


class Restaurant:
    def __init__(self, x: float, y: float):
        self.id = next_id()
        self.pos = (x, y)
        self.name = f"R{self.id}"

    def draw(self, surf: pygame.Surface):
        x, y = int(self.pos[0]), int(self.pos[1])
        pygame.draw.circle(surf, C_REST, (x, y), 14)
        pygame.draw.circle(surf, (255, 120, 120), (x, y), 14, 2)
        # fork & knife icon approximation
        font = pygame.font.SysFont("segoeui", 13, bold=True)
        lbl = font.render("🍴", True, (255,255,255))
        surf.blit(lbl, (x - lbl.get_width()//2, y - lbl.get_height()//2))


class Customer:
    def __init__(self, x: float, y: float):
        self.id = next_id()
        self.pos = (x, y)
        self.name = f"C{self.id}"
        self.flash_timer = 0.0          # flash green when order arrives

    def draw(self, surf: pygame.Surface):
        x, y = int(self.pos[0]), int(self.pos[1])
        color = C_CUST
        if self.flash_timer > 0:
            alpha = min(1.0, self.flash_timer / 0.5)
            color = (
                int(C_CUST[0] + (255-C_CUST[0])*(1-alpha)),
                int(C_CUST[1] + (255-C_CUST[1])*(1-alpha)),
                int(C_CUST[2] + (255-C_CUST[2])*(1-alpha)),
            )
        pygame.draw.circle(surf, color, (x, y), 10)
        pygame.draw.circle(surf, (120, 255, 160), (x, y), 10, 2)

    def update(self, dt: float):
        if self.flash_timer > 0:
            self.flash_timer = max(0.0, self.flash_timer - dt)


class Order:
    def __init__(self, restaurant: Restaurant, customer: Customer):
        self.id = next_id()
        self.restaurant = restaurant
        self.customer = customer
        self.state = OrderState.WAITING
        self.state_name = "WAITING"
        self.prep_time = random.uniform(PREP_TIME_MIN, PREP_TIME_MAX)
        self.prep_elapsed = 0.0
        self.created_at = 0.0
        self.delivered_at: Optional[float] = None

    def update(self, dt: float):
        if self.state == OrderState.PREPARING:
            self.prep_elapsed += dt
            if self.prep_elapsed >= self.prep_time:
                self.state = OrderState.READY
                self.state_name = "READY"

    def assign(self):
        """Called when a courier picks up the order ticket."""
        if self.state == OrderState.WAITING:
            self.state = OrderState.PREPARING
            self.state_name = "PREPARING"

    def deliver(self, sim_time: float):
        self.state = OrderState.DELIVERED
        self.state_name = "DELIVERED"
        self.delivered_at = sim_time


class Courier:
    def __init__(self, x: float, y: float, cid: int):
        self.id = cid
        self.name = f"Courier {cid}"
        self.pos = [x, y]
        self.state = CourierState.IDLE
        self.state_name = "IDLE"
        self.order: Optional[Order] = None
        self.target: Optional[Tuple[float,float]] = None
        self.trail: List[Tuple[float,float]] = []
        self.trail_timer = 0.0
        self.speed = 0.0
        self.total_deliveries = 0
        self.total_distance = 0.0
        # visual pulse
        self.pulse = 0.0

    # ── FSM transition helpers ────────────────

    def assign_order(self, order: Order):
        """IDLE → TO_RESTAURANT"""
        self.order = order
        self.state = CourierState.TO_RESTAURANT
        self.state_name = "TO_RESTAURANT"
        self.target = order.restaurant.pos
        order.assign()

    def _arrive_restaurant(self):
        """TO_RESTAURANT → PICKUP"""
        self.state = CourierState.PICKUP
        self.state_name = "PICKUP"
        self.target = None

    def _pickup_ready(self):
        """PICKUP → TO_CUSTOMER"""
        self.state = CourierState.TO_CUSTOMER
        self.state_name = "TO_CUSTOMER"
        self.target = self.order.customer.pos

    def _deliver(self, sim_time: float):
        """TO_CUSTOMER → IDLE"""
        self.order.deliver(sim_time)
        self.order.customer.flash_timer = 1.5
        self.total_deliveries += 1
        self.order = None
        self.state = CourierState.IDLE
        self.state_name = "IDLE"
        self.target = None

    # ── Per-frame update ──────────────────────

    def update(self, dt: float, sim_time: float, weather: float):
        self.speed = effective_speed(sim_time, weather)
        self.pulse = (self.pulse + dt * 3) % (2 * math.pi)

        # trail recording
        self.trail_timer += dt
        if self.trail_timer > 0.12:
            self.trail_timer = 0.0
            self.trail.append(tuple(self.pos))
            if len(self.trail) > 18:
                self.trail.pop(0)

        # ── FSM logic ──
        if self.state == CourierState.IDLE:
            pass  # dispatcher handles assignment

        elif self.state == CourierState.TO_RESTAURANT:
            self._move_toward(self.target, dt)
            if dist(self.pos, self.target) < PICKUP_RADIUS:
                self._arrive_restaurant()

        elif self.state == CourierState.PICKUP:
            # wait for food
            if self.order and self.order.state == OrderState.READY:
                self._pickup_ready()

        elif self.state == CourierState.TO_CUSTOMER:
            self._move_toward(self.target, dt)
            if dist(self.pos, self.target) < DELIVERY_RADIUS:
                self._deliver(sim_time)

    def _move_toward(self, target: Tuple[float,float], dt: float):
        dx = target[0] - self.pos[0]
        dy = target[1] - self.pos[1]
        nx, ny = norm(dx, dy)
        step = self.speed * dt
        move_d = min(step, math.hypot(dx, dy))
        self.pos[0] += nx * move_d
        self.pos[1] += ny * move_d
        self.total_distance += move_d

    def draw(self, surf: pygame.Surface):
        x, y = int(self.pos[0]), int(self.pos[1])

        # trail
        for i, (tx, ty) in enumerate(self.trail):
            alpha_ratio = i / max(len(self.trail), 1)
            r = int(3 * alpha_ratio)
            if r < 1:
                continue
            col = STATE_COLORS.get(self.state_name, C_COURIER)
            faded = tuple(int(c * alpha_ratio * 0.5) for c in col)
            pygame.draw.circle(surf, faded, (int(tx), int(ty)), r)

        # delivery line
        if self.state == CourierState.TO_CUSTOMER and self.order:
            cx2, cy2 = self.order.customer.pos
            line_surf = pygame.Surface((SIM_W, SIM_H), pygame.SRCALPHA)
            pygame.draw.line(line_surf, (255, 200, 50, 40), (x, y), (int(cx2), int(cy2)), 1)
            surf.blit(line_surf, (0, 0))

        # pulse ring
        col = STATE_COLORS.get(self.state_name, C_COURIER)
        pulse_r = int(16 + 4 * math.sin(self.pulse))
        pygame.draw.circle(surf, col, (x, y), pulse_r, 1)

        # body
        pygame.draw.circle(surf, col, (x, y), 10)
        pygame.draw.circle(surf, (200, 220, 255), (x, y), 10, 2)

        # ID label
        font = pygame.font.SysFont("consolas", 9, bold=True)
        lbl = font.render(str(self.id), True, (255, 255, 255))
        surf.blit(lbl, (x - lbl.get_width()//2, y - lbl.get_height()//2))


# ─────────────────────────────────────────────
#  DISPATCHER  (order assignment)
# ─────────────────────────────────────────────

class Dispatcher:
    """Assigns pending orders to idle couriers (nearest-first)."""

    @staticmethod
    def assign(couriers: List[Courier], orders: List[Order]):
        pending = [o for o in orders if o.state == OrderState.WAITING]
        idle    = [c for c in couriers if c.state == CourierState.IDLE]

        for order in pending:
            if not idle:
                break
            # pick closest idle courier to restaurant
            best = min(idle, key=lambda c: dist(c.pos, order.restaurant.pos))
            best.assign_order(order)
            idle.remove(best)


# ─────────────────────────────────────────────
#  SIMULATION
# ─────────────────────────────────────────────

class Simulation:
    def __init__(self):
        self.sim_time    = 0.0
        self.weather     = random.uniform(0.0, 0.4)
        self.weather_timer = 30.0

        self.restaurants: List[Restaurant] = []
        self.customers:   List[Customer]   = []
        self.couriers:    List[Courier]    = []
        self.orders:      List[Order]      = []

        self.order_timer  = 0.0
        self.delivered_count = 0
        self.order_id_seq = 0

        self._spawn_entities()

    def _spawn_entities(self):
        margin = 60
        for _ in range(NUM_RESTAURANTS):
            self.restaurants.append(Restaurant(
                random.randint(margin, SIM_W - margin),
                random.randint(margin, SIM_H - margin),
            ))
        for _ in range(NUM_CUSTOMERS):
            self.customers.append(Customer(
                random.randint(margin, SIM_W - margin),
                random.randint(margin, SIM_H - margin),
            ))
        for i in range(NUM_COURIERS):
            self.couriers.append(Courier(
                random.randint(margin, SIM_W - margin),
                random.randint(margin, SIM_H - margin),
                i + 1,
            ))

    def _spawn_order(self):
        r = random.choice(self.restaurants)
        c = random.choice(self.customers)
        o = Order(r, c)
        o.created_at = self.sim_time
        self.orders.append(o)

    def update(self, dt: float):
        self.sim_time += dt

        # weather drift
        self.weather_timer -= dt
        if self.weather_timer <= 0:
            self.weather = max(0.0, min(1.0, self.weather + random.uniform(-0.2, 0.2)))
            self.weather_timer = random.uniform(20.0, 50.0)

        # generate orders
        self.order_timer += dt
        if self.order_timer >= ORDER_INTERVAL:
            self.order_timer = 0.0
            self._spawn_order()

        # dispatch
        Dispatcher.assign(self.couriers, self.orders)

        # update orders
        for o in self.orders:
            o.update(dt)

        # update customers
        for c in self.customers:
            c.update(dt)

        # update couriers
        for courier in self.couriers:
            courier.update(dt, self.sim_time, self.weather)

        # count delivered
        self.delivered_count = sum(1 for o in self.orders if o.state == OrderState.DELIVERED)

    # ── Statistics ──────────────────────────

    @property
    def active_orders(self):
        return [o for o in self.orders if o.state != OrderState.DELIVERED]

    @property
    def system_load(self):
        return len(self.active_orders) / max(NUM_COURIERS, 1)

    @property
    def avg_delivery_time(self):
        done = [o for o in self.orders if o.delivered_at is not None]
        if not done:
            return 0.0
        return sum(o.delivered_at - o.created_at for o in done) / len(done)

    @property
    def simulated_hour(self):
        return (self.sim_time / 60.0) % 24


# ─────────────────────────────────────────────
#  RENDERER / UI
# ─────────────────────────────────────────────

class Renderer:
    def __init__(self, screen: pygame.Surface):
        self.screen = screen
        self.font_big   = pygame.font.SysFont("consolas",   22, bold=True)
        self.font_med   = pygame.font.SysFont("consolas",   14, bold=True)
        self.font_sm    = pygame.font.SysFont("consolas",   11)
        self.font_xs    = pygame.font.SysFont("consolas",    9)
        self.sim_surf   = pygame.Surface((SIM_W, SIM_H))
        self.overlay_surf = pygame.Surface((SIM_W, SIM_H), pygame.SRCALPHA)

    def draw_grid(self):
        for x in range(0, SIM_W, 50):
            pygame.draw.line(self.sim_surf, GRID_COL, (x, 0), (x, SIM_H))
        for y in range(0, SIM_H, 50):
            pygame.draw.line(self.sim_surf, GRID_COL, (0, y), (SIM_W, y))

    def draw_sidebar(self, sim: Simulation):
        sx = SIM_W
        # background
        pygame.draw.rect(self.screen, PANEL_BG, (sx, 0, SIDEBAR_W, HEIGHT))
        pygame.draw.line(self.screen, PANEL_BORDER, (sx, 0), (sx, HEIGHT), 1)

        y = 18
        def text(msg, col=C_TEXT, font=None):
            nonlocal y
            f = font or self.font_sm
            s = f.render(msg, True, col)
            self.screen.blit(s, (sx + 14, y))
            y += s.get_height() + 3

        def sep(height=8):
            nonlocal y
            y += height // 2
            pygame.draw.line(self.screen, PANEL_BORDER, (sx+10, y), (sx+SIDEBAR_W-10, y), 1)
            y += height // 2

        def bar(label, value, max_val, color):
            nonlocal y
            text(label, C_LABEL)
            bw = SIDEBAR_W - 28
            bh = 8
            pygame.draw.rect(self.screen, (30,38,50), (sx+14, y, bw, bh), border_radius=4)
            fill = int(bw * min(value / max(max_val,0.001), 1.0))
            if fill > 0:
                pygame.draw.rect(self.screen, color, (sx+14, y, fill, bh), border_radius=4)
            y += bh + 6

        # ── Title ──
        text("FOOD DELIVERY", C_ACCENT, self.font_big)
        text("SIMULATION", C_ACCENT, self.font_med)
        sep(10)

        # ── Time & weather ──
        h = sim.simulated_hour
        hh = int(h); mm = int((h - hh) * 60)
        text(f"Time  {hh:02d}:{mm:02d}", C_TEXT, self.font_med)
        rush_lvl = traffic_factor(sim.sim_time, sim.weather)
        weather_str = "☀ Sunny" if sim.weather < 0.2 else ("🌧 Rainy" if sim.weather > 0.5 else "⛅ Cloudy")
        text(f"Weather  {weather_str}", C_TEXT)
        bar("Traffic congestion", rush_lvl, 1.5, C_WARN)
        spd = effective_speed(sim.sim_time, sim.weather)
        text(f"Eff. Speed  {spd:.1f} px/s", C_LABEL)
        sep()

        # ── Orders ──
        text("ORDERS", C_ACCENT, self.font_med)
        text(f"Total created    {len(sim.orders)}", C_TEXT)
        text(f"Active           {len(sim.active_orders)}", C_TEXT)
        text(f"Delivered        {sim.delivered_count}", C_OK)
        text(f"Avg delivery     {sim.avg_delivery_time:.1f}s", C_LABEL)
        bar("System load", sim.system_load, 3.0, C_WARN)
        sep()

        # ── Couriers ──
        text("COURIERS", C_ACCENT, self.font_med)
        for c in sim.couriers:
            sc = STATE_COLORS.get(c.state_name, C_COURIER)
            state_short = c.state_name.replace("_", " ")
            line = f"#{c.id:<2} {state_short:<16}"
            t = self.font_xs.render(line, True, sc)
            self.screen.blit(t, (sx + 14, y))
            d_t = self.font_xs.render(f"del:{c.total_deliveries}", True, C_LABEL)
            self.screen.blit(d_t, (sx + SIDEBAR_W - d_t.get_width() - 14, y))
            y += t.get_height() + 2
        sep()

        # ── Order queue ──
        text("ORDER QUEUE", C_ACCENT, self.font_med)
        active = sim.active_orders[-8:]
        for o in active:
            sc = ORDER_STATE_COLORS.get(o.state_name, C_TEXT)
            age = sim.sim_time - o.created_at
            msg = f"#{o.id:<3} {o.state_name:<10} {age:5.1f}s"
            t = self.font_xs.render(msg, True, sc)
            self.screen.blit(t, (sx + 14, y))
            y += t.get_height() + 2

        # ── Legend ──
        sep(14)
        text("LEGEND", C_ACCENT, self.font_med)
        legend = [
            (C_REST,    "Restaurant"),
            (C_CUST,    "Customer"),
            (C_COURIER, "Courier"),
        ]
        for col, lbl in legend:
            pygame.draw.circle(self.screen, col, (sx + 22, y + 5), 6)
            t = self.font_xs.render(lbl, True, C_TEXT)
            self.screen.blit(t, (sx + 34, y))
            y += 14

    def draw_sim(self, sim: Simulation):
        self.sim_surf.fill(BG)
        self.draw_grid()

        # draw restaurants
        for r in sim.restaurants:
            r.draw(self.sim_surf)

        # draw customers
        for c in sim.customers:
            c.draw(self.sim_surf)

        # draw courier trails + bodies
        for courier in sim.couriers:
            courier.draw(self.sim_surf)

        # draw state labels for couriers
        for courier in sim.couriers:
            if courier.state != CourierState.IDLE:
                x, y = int(courier.pos[0]), int(courier.pos[1])
                sc = STATE_COLORS.get(courier.state_name, C_COURIER)
                lbl = self.font_xs.render(courier.state_name.replace("_"," "), True, sc)
                self.screen.blit  # placeholder
                self.sim_surf.blit(lbl, (x - lbl.get_width()//2, y - 22))

        self.screen.blit(self.sim_surf, (0, 0))

    def render(self, sim: Simulation):
        self.draw_sim(sim)
        self.draw_sidebar(sim)
        pygame.display.flip()


# ─────────────────────────────────────────────
#  MAIN
# ─────────────────────────────────────────────

def main():
    pygame.init()
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Food Delivery Simulation — Agent-Based + FSM")
    clock = pygame.time.Clock()

    sim      = Simulation()
    renderer = Renderer(screen)

    paused = False
    speed_mult = 1.0

    running = True
    while running:
        dt_real = clock.tick(FPS) / 1000.0
        dt = dt_real * speed_mult

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    running = False
                elif event.key == pygame.K_SPACE:
                    paused = not paused
                elif event.key == pygame.K_UP:
                    speed_mult = min(speed_mult * 1.5, 8.0)
                elif event.key == pygame.K_DOWN:
                    speed_mult = max(speed_mult / 1.5, 0.25)
                elif event.key == pygame.K_r:
                    sim = Simulation()

        if not paused:
            sim.update(dt)

        renderer.render(sim)

        # HUD overlay
        font = pygame.font.SysFont("consolas", 11)
        hints = [
            f"SPACE=pause  ↑↓=speed({speed_mult:.1f}x)  R=reset  ESC=quit",
            f"{'⏸ PAUSED' if paused else '▶ RUNNING'}  |  sim time: {sim.sim_time:.1f}s",
        ]
        for i, h in enumerate(hints):
            s = font.render(h, True, (80, 100, 130))
            screen.blit(s, (8, HEIGHT - 28 + i * 13))

        pygame.display.flip()

    pygame.quit()


if __name__ == "__main__":
    main()