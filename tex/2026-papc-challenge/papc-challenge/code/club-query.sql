-- Which CS members attended the session on Lists?
SELECT DISTINCT m.name
FROM Member m
  JOIN Attended a ON m.name = a.name
  JOIN Session  s ON a.week = s.week
WHERE m.dept = 'CS' AND s.topic = 'Lists';
