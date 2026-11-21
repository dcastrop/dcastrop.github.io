SELECT o.id
FROM orders o JOIN users u ON o.user_id = u.id
WHERE u.country = 'UK';
-- the optimiser filters users before joining:
--   filter(join(orders, users)) = join(orders, filter(users))
