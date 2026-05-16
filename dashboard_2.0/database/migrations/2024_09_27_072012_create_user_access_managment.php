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
        if(!Schema::hasTable('user_access_managment'))
        {
            Schema::create('user_access_managment', function (Blueprint $table) {
                $table->id();
                $table->string('role_id');
                $table->string('user_id');
                $table->string('type');
                $table->longText('data');
                $table->enum('status', ['Y', 'N'])->default('Y');
                $table->timestamps();
                $table->softDeletes();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('user_access_managment');
    }
};
