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
        Schema::create('broadcast_module_changes', function (Blueprint $table) {
            $table->id();
            $table->string('broadcast_name');
            $table->integer('user_type');
            $table->enum('category',['Policy Changes', 'Reminders', 'Alerts', 'Events', 'News and Updates']);
            $table->enum('content_type',['Video','Blog','Document','Content']);
            $table->string('title');
            $table->text('description')->nullable();
            $table->string('link')->nullable();
            $table->string('image')->nullable();
            $table->integer('choose_role');
            $table->enum('priority',['High','Medium','Low']);
            $table->date('from_date');
            $table->date('to_date');
            $table->enum('status',['Y','N']);
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('broadcast_module_new_changes');
    }
};
