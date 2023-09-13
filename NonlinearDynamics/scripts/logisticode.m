% clear everything
clearvars; close all;

% define logistic ode as f(x) = dx/dt
lambda = 2; % param

% logistic = @(x, n) lambda*x*(1-x);


tspan = [0 1.5];

y0s = {-1,-0.5, 0, 0.1, 0.5, 1, 1.5, 2};


for i=1:length(y0s)
    y0 = y0s{i};
    [t,y] = ode45(@(t,y) lambda*y*(1-y), tspan, y0);
    plot(t,y);
   
    text(0.1,y(7,1), sprintf('x_0=%s',num2str(y0, 2)));
    xlim([0,1.5])
    ylim([-2 2])
    hold on
end
hold off
