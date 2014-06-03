namespace $rootnamespace$.Controllers.Users
{
    using System.Web.Mvc;
    using Core.Interfaces.Service;

    public partial class UsersController : Controller
    {
        protected readonly IUserService UserService;

        public UsersController(IUserService userService)
        {
            UserService = userService;
        }
    }
}
