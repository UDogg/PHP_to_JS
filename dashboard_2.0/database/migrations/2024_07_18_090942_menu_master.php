<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        //
        if(!Schema::hasTable('MenuMaster'))
        {
            Schema::create('MenuMaster', function (Blueprint $table) {
                $table->id();
                $table->string('menu');
                $table->string('route')->nullable();
                $table->string('icon')->nullable();
                $table->integer('menuId')->comment("main menu id if this menu is a child menu else parent menu id is null")->nullable()->default(null);
                $table->integer("subMenuId")->nullable()->comment('if this menu is a sub menu of any other sub menu')->default(null);
                $table->tinyInteger('status')->default(1);
                $table->softDeletes();
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::dropIfExists('MenuMaster');
    }
};
