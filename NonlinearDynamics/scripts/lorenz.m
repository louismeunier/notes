sigma = 10;
beta = 8/3;

% iterate different rhos
for rho=1:50:1000
    f = @(t,a) [-sigma*a(1) + sigma*a(2); rho*a(1) - a(2) - a(1)*a(3); -beta*a(3) + a(1)*a(2)];
    [t,a] = ode45(f,[0 100],[1 1 10]);     % Runge-Kutta 4th/5th order ODE solver
    plot3(a(:,1),a(:,2),a(:,3))
    hold on
    
    plot3(sqrt(beta*(rho-1)), sqrt(beta*(rho-1)), rho-1, 'o', MarkerSize=7)
    plot3(-sqrt(beta*(rho-1)), -sqrt(beta*(rho-1)), rho-1, 'o', MarkerSize=7)
    plot3(0, 0, 0, 'o', MarkerSize=7)
    % f_sim = @(t,a) [-sigma*a(1) + sigma*a(2); rho*a(1)-a(2); -beta*a(3)];
    % [t_sim, a_sim] = ode45(f_sim,[0 100],[1 1 1]);
    % plot3(a_sim(:,1), a_sim(:,2), a_sim(:,3));
    % xlim([-5,5])
    % ylim([-5,5])
    % zlim([-,20])
end
hold off